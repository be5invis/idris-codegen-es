module Js.ServiceTypes

import public Js.Json
import public Data.List


public export
data ServiceTy = RPCServiceTy Type Type
               | FeedServiceTy Type Type

public export
data EncoderDecoder a = MkEncoderDecoder (a -> String) (String -> Either String a)

public export
data Service : String -> ServiceTy -> Type where
  RPCService : (s:String) -> EncoderDecoder a -> EncoderDecoder b -> Service s (RPCServiceTy a b)

public export
data ServiceGroup : List (String, ServiceTy) -> Type where
  Nil : ServiceGroup []
  (::) : Service s t -> ServiceGroup ts -> ServiceGroup ((s,t)::ts)

export
decode : EncoderDecoder a -> String -> Either String a
decode (MkEncoderDecoder _ d) x = d x

export
encode : EncoderDecoder a -> a -> String
encode (MkEncoderDecoder e _) x = e x

public export
getService : (name:String) -> ServiceGroup ts -> Elem (name, s) ts -> Service name s
getService name (x :: xs) Here = x
getService name (x :: xs) (There p') = getService name xs p'

export
jsonEncoderDecoder : BothJson a => EncoderDecoder a
jsonEncoderDecoder = MkEncoderDecoder encode decode
