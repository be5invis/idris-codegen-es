module Js.Node

import public Js.ASync
import public Js.ServiceTypes
import Data.SortedMap


require : String -> JS_IO Ptr
require s = jscall "require(%0)" (String -> JS_IO Ptr) s

export
readFileSync : String -> JS_IO String
readFileSync file =
  do
    fs <- require "fs"
    jscall "%0.readFileSync(%1)" (Ptr -> String -> JS_IO String) fs file

export
data Request = MkRequest Ptr

end : String -> Request -> JS_IO ()
end s (MkRequest p) =
  do
    jscall "%0[1].end(%1)" (Ptr -> String -> JS_IO ()) p s

url : Request -> JS_IO String
url (MkRequest p) = jscall "%0[0].url" (Ptr -> JS_IO String) p

method : Request -> JS_IO String
method (MkRequest r) = jscall "%0[0].method" (Ptr -> JS_IO String) r

error : Int -> Request -> JS_IO ()
error 404 (MkRequest p) =
  do
    jscall "%0[1].writeHead(404,{'Content-Type': 'text/plain'})" (Ptr->JS_IO ()) p
    jscall "%0[1].end(%1)" (Ptr -> String -> JS_IO ()) p "404 Not Found"
error 400 (MkRequest p) =
  do
    jscall "%0[1].writeHead(400,{'Content-Type': 'text/plain'})" (Ptr->JS_IO ()) p
    jscall "%0[1].end(%1)" (Ptr -> String -> JS_IO ()) p "400 Bad Request"

export
data HttpHandler = HandleGet String (JS_IO String)
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
        --    liftJS_IO $ putStr' x
        --    liftJS_IO $ putStr' z
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

procInput : Request -> (String -> ASync String) -> String -> JS_IO ()
procInput (MkRequest p) f body =
  do
    let async = f body
    setASync procRes async
  where
    procRes s =
      do
        jscall "%0[1].writeHead(200,{'Content-Type': 'text/plain'})" (Ptr -> JS_IO ()) p
        jscall "%0[1].end(%1)" (Ptr -> String -> JS_IO ()) p s


procReqRaw : SortedMap String HttpHandler -> Request -> JS_IO ()
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
          (Ptr -> (JsFn (String -> JS_IO ())) -> JS_IO())
          p
          (MkJsFn $ procInput r x)

export
runServer : Int -> List HttpHandler -> JS_IO ()
runServer port services =
  do
    http <- require "http"
    server <- jscall
                  "%0.createServer(function(req, res){return %1([req,res])})"
                  (Ptr -> (JsFn (Ptr -> JS_IO ())) -> JS_IO Ptr )
                  http
                  (MkJsFn $ \x => procReqRaw servMap (MkRequest x))
    jscall
      "%1.listen(%0, function(){console.log('Server listening on: http://localhost:%s', %0)})"
      (Int -> Ptr -> JS_IO ())
      port
      server
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
                       (Ptr -> Ptr -> (JsFn (String -> JS_IO ())) -> JS_IO Ptr)
                       http
                       options
                       (MkJsFn g)
                    case body of
                      Nothing => pure ()
                      Just z => jscall "%0.write(%1)" (Ptr -> String -> JS_IO ()) req z
                    jscall "%0.end()" (Ptr -> JS_IO ()) req
  where
    getOpts =
      jscall
        "{hostname:%0, port: %1, path: %2, method: %3}"
        (String -> Int -> String -> String -> JS_IO Ptr)
        host port path method

export
httpGet : String -> Int -> String -> ASync String
httpGet host port path = httpRequest host port path "GET" Nothing
