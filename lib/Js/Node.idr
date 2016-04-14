module Js.Node

import public Js.IO
import public Js.ServiceTypes
import Data.SortedMap


require : String -> JSIO Ptr
require s = jscall "require(%0)" (String -> JSIO Ptr) s

export
readFileSync : String -> JSIO String
readFileSync file =
  do
    fs <- require "fs"
    jscall "%0.readFileSync(%1)" (Ptr -> String -> JSIO String) fs file

export
data Request = MkRequest Ptr

end : String -> Request -> JSIO ()
end s (MkRequest p) =
  do
    jscall "%0[1].end(%1)" (Ptr -> String -> JSIO ()) p s

url : Request -> JSIO String
url (MkRequest p) = jscall "%0[0].url" (Ptr -> JSIO String) p

method : Request -> JSIO String
method (MkRequest r) = jscall "%0[0].method" (Ptr -> JSIO String) r

error : Int -> Request -> JSIO ()
error 404 (MkRequest p) =
  do
    jscall "%0[1].writeHead(404,{'Content-Type': 'text/plain'})" (Ptr->JSIO ()) p
    jscall "%0[1].end(%1)" (Ptr -> String -> JSIO ()) p "404 Not Found"
error 400 (MkRequest p) =
  do
    jscall "%0[1].writeHead(400,{'Content-Type': 'text/plain'})" (Ptr->JSIO ()) p
    jscall "%0[1].end(%1)" (Ptr -> String -> JSIO ()) p "400 Bad Request"

export
data HttpHandler = HandleGet String (JSIO String)
                 | HandlePost String (String -> ASync String)

handlerSelector : HttpHandler -> String
handlerSelector (HandleGet s _) = "GET" ++ s
handlerSelector (HandlePost s _) = "POST" ++ s

serviceTy : Service -> Type
serviceTy (MkService _ a b _) = (a -> ASync b)

makeRawServ : (s:Service) -> serviceTy s -> HttpHandler
makeRawServ (MkService s _ _ (dec, _, _, enc)) f =
  HandlePost s $ \x =>
        case dec x of
        --  Left z => do
        --    liftJSIO $ putStr' x
        --    liftJSIO $ putStr' z
        --    pure $ Left 400
          Right z =>
            map enc $ f z

export
MakeServicesTy : List Service -> Type
MakeServicesTy [] = List HttpHandler
MakeServicesTy (x::xs) = serviceTy x -> MakeServicesTy xs

makeServices' : (ls : List Service) -> List HttpHandler -> MakeServicesTy ls
makeServices' [] acc = acc
makeServices' (x::xs) acc = \next => makeServices' xs (makeRawServ x next :: acc )

export
makeServices : (s : List Service) -> MakeServicesTy s
makeServices x = makeServices' x []

procInput : Request -> (String -> ASync String) -> String -> JSIO ()
procInput (MkRequest p) f body =
  do
    let async = f body
    setASync procRes async
  where
    procRes s =
      do
        jscall "%0[1].writeHead(200,{'Content-Type': 'text/plain'})" (Ptr -> JSIO ()) p
        jscall "%0[1].end(%1)" (Ptr -> String -> JSIO ()) p s


procReqRaw : SortedMap String HttpHandler -> Request -> JSIO ()
procReqRaw handlers r@(MkRequest p) = do
  u <- url r
  m <- method r
  let sel = m ++ u
  case lookup sel handlers of
    Nothing => error 404 r
    Just (HandleGet _ x) =>
      do
        result <- x
        end result r
    Just (HandlePost _ x) =>
      do
        jscall
          ("(function(req){" ++
           "var body='';" ++
           "req[0].on('data', function(data){body+=data} );" ++
           "req[0].on('end', function(){%1(body)} );" ++
           "})(%0)")
          (Ptr -> (String -> JSIO ()) -> JSIO())
          p
          (procInput r x)

export
runServer : Int -> List HttpHandler -> JSIO ()
runServer port services =
  do
    http <- require "http"
    server <- jscall
                  "%0.createServer(function(req, res){return %1([req,res])})"
                  (Ptr -> (Ptr -> JSIO ()) -> JSIO Ptr )
                  http
                  (\x => procReqRaw servMap (MkRequest x))
    jscall "%1.listen(%0, function(){console.log('Server listening on: http://localhost:%s', %0)})" (Int -> Ptr -> JSIO ()) port server
  where
    servMap : SortedMap String (HttpHandler)
    servMap = fromList $ zip (map handlerSelector services) services


httpRequest : String -> Int -> String -> String -> Maybe String -> ASync String
httpRequest host port path method body =
  MkASync $ \g => do
                    http <- require "http"
                    options <- getOpts
                    req <- jscall
                      ("%0.request(%1, function(res){ " ++
                       "  var body = '';" ++
                       "  res.on('data', function(data){body+=data});" ++
                       "  res.on('end', function(){console.log(body);%2(body)})" ++
                       "})")
                       (Ptr -> Ptr -> (String -> JSIO ()) -> JSIO Ptr)
                       http
                       options
                       g
                    case body of
                      Nothing => pure ()
                      Just z => jscall "%0.write(%1)" (Ptr -> String -> JSIO ()) req z
                    jscall "%0.end()" (Ptr -> JSIO ()) req
  where
    getOpts =
      jscall
        "{hostname:%0, port: %1, path: %2, method: %3}"
        (String -> Int -> String -> String -> JSIO Ptr)
        host port path method

export
httpGet : String -> Int -> String -> ASync String
httpGet host port path = httpRequest host port path "GET" Nothing
