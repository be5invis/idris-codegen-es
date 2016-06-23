module Js.ServiceTypes

import public Js.Json


public export
data Service : Type where
  MkService : String -> (a:Type) -> (b:Type)
      -> ((String -> Either String a), (a->String), (String -> Either String b), (b->String)) -> Service

{-
export
typeInput : Service -> Type
typeInput (MkService _ x _ _) = x

export
typeOutput : Service -> Type
typeOutput (MkService _ _ x _) = x
-}

public export
getServ : String -> List Service -> Maybe Service
getServ _ [] = Nothing
getServ n (s@(MkService n2 _ _ _ )::rest) = if n == n2 then Just s else getServ n rest

export
jsonServ : (BothJson a, BothJson b) => ((String -> Either String a), (a->String), (String -> Either String b), (b->String))
jsonServ = (decode, encode, decode, encode)
