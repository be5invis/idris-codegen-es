module SimpleData

import public Data.HVect
import public Data.Vect
import public Js.ASync
import public Js.Json

public export
data Label : String -> Type -> Type where
  MkLabel : a -> Label s a

public export
data Alt : Vect n Type -> Type where
  MkAlt : (Elem t ts) -> t -> Alt ts

public export
AltExpand: Alt xs -> Alt (x::xs)
AltExpand (MkAlt p x) = MkAlt (There p) x

public export
data SDataTy : Type where
  SString : SDataTy
  SUnit : SDataTy
  SList : SDataTy -> SDataTy
  STuple : SDataTy -> SDataTy -> SDataTy
  SObj : List (String, SDataTy) -> SDataTy
  SAlt : List (String, SDataTy) -> SDataTy
  SEither : SDataTy -> SDataTy -> SDataTy
  SMaybe : SDataTy -> SDataTy
  SJson : SDataTy

export
ToJson SDataTy where
  toJson SString = JsonArray [JsonString "SString"]
  toJson SUnit = JsonArray [JsonString "SUnit"]
  toJson (SList x) = JsonArray [JsonString "SList", toJson x]
  toJson (STuple x y) = JsonArray [JsonString "STuple", toJson x, toJson y]
  toJson (SObj x) = JsonArray [JsonString "SObj", toJson x]
  toJson (SAlt x) = JsonArray [JsonString "SAlt", toJson x]
  toJson (SEither x y) = JsonArray [JsonString "SEither", toJson x, toJson y]
  toJson (SMaybe x) = JsonArray [JsonString "SMaybe", toJson x]
  toJson SJson = JsonArray [JsonString "SJson"]

export
FromJson SDataTy where
  fromJson (JsonArray [JsonString "SString"]) = Right SString
  fromJson (JsonArray [JsonString "SUnit"]) = Right SUnit
  fromJson (JsonArray [JsonString "SList", x]) = SList <$> fromJson x
  fromJson (JsonArray [JsonString "STuple", x, y]) = STuple <$> fromJson x <*> fromJson y
  fromJson (JsonArray [JsonString "SObj", x]) = SObj <$> fromJson x
  fromJson (JsonArray [JsonString "SAlt", x]) = SAlt <$> fromJson x
  fromJson (JsonArray [JsonString "SEither", x, y]) = SEither <$> fromJson x <*> fromJson y
  fromJson (JsonArray [JsonString "SMaybe", x]) = SMaybe <$> fromJson x
  fromJson (JsonArray [JsonString "SJson"]) = Right SJson


public export
SDataObj : Type
SDataObj = List (String, SDataTy)

public export
total
iSDataTy : SDataTy -> Type
iSDataTy SString = String
iSDataTy SUnit = ()
iSDataTy (SList x) = List (iSDataTy x)
iSDataTy (STuple x y) = (iSDataTy x, iSDataTy y)
iSDataTy (SObj x) = assert_total $ HVect $ fromList $ map (\z => Label (fst z) (iSDataTy $ snd z) ) x
iSDataTy (SAlt x) = assert_total $ Alt $ fromList $ map (\z => Label (fst z) (iSDataTy $ snd z) ) x
iSDataTy (SEither x y) = Either (iSDataTy x) (iSDataTy y)
iSDataTy (SMaybe x) = Maybe (iSDataTy x)
iSDataTy SJson = JsonValue


public export
total
iSDataObj : SDataObj -> Type
iSDataObj x = iSDataTy $ SObj x

export
encodeJS : (a:SDataTy) -> iSDataTy a -> JS_IO Ptr
encodeJS SString s = jscall "%0" (String -> JS_IO Ptr) s

export
decodeJS : (a:SDataTy) -> Ptr -> JS_IO (Either String (iSDataTy a))
decodeJS SString p =
  do
    c <- jscall "(typeof %0 === 'string')+0" (Ptr -> JS_IO Int) p
    if c == 1 then
      Right <$> jscall "%0" (Ptr -> JS_IO String) p
      else pure $ Left "decodeVal: Not a String"
