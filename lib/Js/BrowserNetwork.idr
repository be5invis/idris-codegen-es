module Js.BrowserNetwork

import Js.BrowserForeigns
import public Js.ServiceTypes

export
httpGet : String -> ASync String
httpGet url = MkASync $ httpGet_raw url

export
httpPost : String -> String -> ASync String
httpPost url body = MkASync $ httpPost_raw url body

export
callRPC : ServiceGroup ts -> (name:String) -> Elem (name, RPCServiceTy a b) ts -> a -> ASync b
callRPC group name p val =
  let (RPCService _ e1 e2) = getService name group p
  in do
    res <- httpPost name (encode e1 val)
    case decode e2 res of
      Right x => pure x
      Left err => debugError err
