module Js.Node

import public Js.ASync
import public Js.ServiceTypes
import Data.SortedMap


require : String -> JS_IO Ptr
require s = jscall "require(%0)" (String -> JS_IO Ptr) s

export
err2Either : ASync Ptr -> ASync (Either String Ptr)
err2Either x =
  do
    y <- x
    errQ <- liftJS_IO $ jscall "%0[0] ? 1 : 0" (Ptr -> JS_IO Int) y
    if errQ == 1 then
      do
        msg <- liftJS_IO $ jscall "%0[0] + ''" (Ptr -> JS_IO String) y
        pure $ Left msg
      else
        do
          res <- liftJS_IO $ jscall "%0[1]" (Ptr -> JS_IO Ptr) y
          pure $ Right res

export
handleErr : ASync Ptr -> ASync Ptr
handleErr x  =
  do
    z <- err2Either x
    case z of
      Left e => error e
      Right res => pure res

export
readFileSync : String -> JS_IO String
readFileSync file =
  do
    fs <- require "fs"
    jscall "%0.readFileSync(%1)" (Ptr -> String -> JS_IO String) fs file

export
readFile : String -> ASync String
readFile f =
  do
    map (\x => the String (believe_me x)) $ handleErr $ MkASync $ \proc =>
      do
        jscall
          "require('fs').readFile(%0, 'utf8', function(e,c){%1([e,c])} )"
          (String -> JsFn (Ptr -> JS_IO ()) -> JS_IO () )
          f
          (MkJsFn $ proc)

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

public export
data HttpHandler = HandleGet String (JS_IO String)
                 | HandlePost String (String -> ASync String)

public export
data WSHandler = HandleWSFeed String (String -> Cursor String)
--

handlerSelector : HttpHandler -> String
handlerSelector (HandleGet s _) = "GET" ++ s
handlerSelector (HandlePost s _) = "POST" ++ s

total
public export
ImplementationTy : Type -> ServiceTy -> Type
ImplementationTy t (RPCServiceTy a b) = (t -> a -> ASync b)
ImplementationTy t (FeedServiceTy a b) = (t -> a -> Cursor b)

makeRawServ : t -> Service name st -> ImplementationTy t st -> Either HttpHandler WSHandler
makeRawServ context (RPCService name e1 e2) f =
  Left $ HandlePost name $ \x =>
        case decode e1 x of
          --Left z => do
          --  liftJS_IO $ putStr' x
          --  liftJS_IO $ putStr' z
          --  pure $ Left 400
          Right z =>
            encode e2 <$> f context z
makeRawServ context (FeedService name e1 e2) f =
  Right $ HandleWSFeed name $ \x =>
        case decode e1 x of
          --Left z => do
          --  liftJS_IO $ putStr' x
          --  liftJS_IO $ putStr' z
          --  pure $ Left 400
          Right z =>
            encode e2 <$> f context z

addRawServ : t -> Service name st -> ImplementationTy t st ->
              (List HttpHandler, List WSHandler) -> (List HttpHandler, List WSHandler)
addRawServ x y z (w, k) =
  case makeRawServ x y z of
    Left u => (u::w, k)
    Right u => (w, u::k)

public export
MakeServicesTy : Type -> List (String, ServiceTy) -> Type
MakeServicesTy t [] = (List HttpHandler, List WSHandler)
MakeServicesTy t ((_,st)::xs) = ImplementationTy t st -> MakeServicesTy t xs

makeServices' : t -> ServiceGroup ts -> (List HttpHandler, List WSHandler) -> MakeServicesTy t ts
makeServices' _ [] acc = acc
makeServices' ctx (x::xs) acc = \next => makeServices' ctx xs (addRawServ ctx x next acc )

export
makeServices : ServiceGroup ts -> t -> MakeServicesTy t ts
makeServices x ctx = makeServices' ctx x ([],[])

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

setupWS : Ptr -> Ptr -> List WSHandler -> JS_IO ()
setupWS url wss wsservices =
  do
    jscall
      ("%0.on('connection', function connection(ws){" ++
      " console.log(%1.parse(ws.upgradeReq.url, true));" ++
      "})")
      (Ptr -> Ptr -> JS_IO ())
      wss
      url

export
runServer : Int -> List HttpHandler -> List WSHandler -> ASync ()
runServer port services wsservices =
  do
    http <- liftJS_IO $ require "http"
    url <- liftJS_IO $ require "url"
    webSocketServer <- liftJS_IO $ jscall "require('ws').Server" (() -> JS_IO Ptr) ()
    server <- liftJS_IO $ jscall
                  "%0.createServer(function(req, res){return %1([req,res])})"
                  (Ptr -> (JsFn (Ptr -> JS_IO ())) -> JS_IO Ptr )
                  http
                  (MkJsFn $ \x => procReqRaw servMap (MkRequest x))
    wss <- liftJS_IO $ jscall "new %0({server: %1})" (Ptr -> Ptr -> JS_IO Ptr) webSocketServer server
    liftJS_IO $ setupWS url wss wsservices
    MkASync $ \proc => jscall
      "%1.listen(%0, %2)"
      (Int -> Ptr -> JsFn (() -> JS_IO ()) -> JS_IO ())
      port
      server
      (MkJsFn proc)
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
