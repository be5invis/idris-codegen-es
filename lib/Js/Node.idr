module Js.Node

import public Js.IO
import public Js.ServiceTypes
import Data.SortedMap


require : String -> JSIO Ptr
require s = jscall "require(%0)" (String -> JSIO Ptr) s

public
readFileSync : String -> JSIO String
readFileSync file =
  do
    fs <- require "fs"
    jscall "%0.readFileSync(%1)" (Ptr -> String -> JSIO String) fs file

abstract
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

public
data HttpHandler = HandleGet String (JSIO String)
                 | HandlePost String (String -> ASync (Either Int String) ) -- JSIO (Either String String) )

handlerSelector : HttpHandler -> String
handlerSelector (HandleGet s _) = "GET" ++ s
handlerSelector (HandlePost s _) = "POST" ++ s

serviceTy : Service -> Type
serviceTy (MkService _ a b _) = (a -> ASync (Either Int b))

makeRawServ : (s:Service) -> serviceTy s -> HttpHandler
makeRawServ (MkService s _ _ (dec, _, _, enc)) f =
  HandlePost s $ \x =>
        case dec x of
          Left z => do
            liftJSIO $ putStr' x
            liftJSIO $ putStr' z
            pure $ Left 400
          Right z =>
            map (map enc) $ f z

public
MakeServicesTy : List Service -> Type
MakeServicesTy [] = List HttpHandler
MakeServicesTy (x::xs) = serviceTy x -> MakeServicesTy xs

makeServices' : (ls : List Service) -> List HttpHandler -> MakeServicesTy ls
makeServices' [] acc = acc
makeServices' (x::xs) acc = \next => makeServices' xs (makeRawServ x next :: acc )

public
makeServices : (s : List Service) -> MakeServicesTy s
makeServices x = makeServices' x []

procInput : Request -> ( String -> ASync (Either Int String)) -> String -> JSIO ()
procInput (MkRequest p) f body =
  do
    let async = f body
    setASync procRes async
  where
    procRes x =
      case x of
        Left i => error i $ MkRequest p
        Right s =>
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
        procInput r x "\"ola\""
        jscall
          ("(function(req){" ++
           "var body='';" ++
           "req[0].on('data', function(data){body+=data} );" ++
           "req[0].on('end', function(){%1(body)} );" ++
           "})(%0)")
          (Ptr -> (String -> JSIO ()) -> JSIO())
          p
          (procInput r x)

public
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
