module SimpleData

import public Data.HVect
import public Data.Vect
import public Js.ASync
import public Js.Json

public export
data Label : String -> Type -> Type where
  MkLabel : (s : String) -> a -> Label s a

infixr 2 :=

export
(:=) : (s : String) -> a -> Label s a
(:=) x y = MkLabel x y

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
  SObj : Vect k (String, SDataTy) -> SDataTy
  SAlt : Vect k (String, SDataTy) -> SDataTy
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
  fromJson (JsonArray [JsonString "SObj", JsonArray x]) =
    SObj <$> the (Either String (Vect (length x) (String, SDataTy))) (fromJson $ JsonArray x)
  fromJson (JsonArray [JsonString "SAlt", JsonArray x]) =
    SAlt <$> the (Either String (Vect (length x) (String, SDataTy))) (fromJson $ JsonArray x)
  fromJson (JsonArray [JsonString "SEither", x, y]) = SEither <$> fromJson x <*> fromJson y
  fromJson (JsonArray [JsonString "SMaybe", x]) = SMaybe <$> fromJson x
  fromJson (JsonArray [JsonString "SJson"]) = Right SJson


public export
SDataObj : {n:Nat} -> Type
SDataObj {n} = Vect n (String, SDataTy)

mutual
  public export total
  SObjTy : Vect k (String, SDataTy) -> Vect k Type
  SObjTy [] = []
  SObjTy ((s, x)::xs) = assert_total $ Label s (ISDataTy x) :: SObjTy xs

  public export  total
  SAltTy : Vect k (String, SDataTy) -> Vect k Type
  SAltTy [] = []
  SAltTy ((s, x)::xs) = assert_total $ Label s (ISDataTy x) :: SAltTy xs

  public export total
  ISDataTy : SDataTy -> Type
  ISDataTy SString = String
  ISDataTy SUnit = ()
  ISDataTy (SList x) = List (ISDataTy x)
  ISDataTy (STuple x y) = (ISDataTy x, ISDataTy y)
  ISDataTy (SObj x) = HVect (SObjTy x)
  ISDataTy (SAlt x) = Alt (SAltTy x)
  ISDataTy (SEither x y) = Either (ISDataTy x) (ISDataTy y)
  ISDataTy (SMaybe x) = Maybe (ISDataTy x)
  ISDataTy SJson = JsonValue


public export total
ISDataObj : SDataObj -> Type
ISDataObj x = ISDataTy $ SObj x

mutual
  export
  jsonValueToJS : JsonValue -> JS_IO Ptr
  jsonValueToJS (JsonString s) = pure $ believe_me s
  jsonValueToJS (JsonNumber d) = pure $ believe_me d
  jsonValueToJS (JsonBool True) = jscall "true" (() -> JS_IO Ptr) ()
  jsonValueToJS (JsonBool False) = jscall "false" (() -> JS_IO Ptr) ()
  jsonValueToJS JsonNull = jscall "null" (() -> JS_IO Ptr) ()
  jsonValueToJS (JsonArray []) =
    jscall "[]" (() -> JS_IO Ptr) ()
  jsonValueToJS (JsonArray (x::xs)) =
    do
      ys <- jsonValueToJS $ JsonArray xs
      y <- jsonValueToJS x
      jscall "%1.unshift(%0)" (Ptr -> Ptr -> JS_IO Ptr) y ys
      pure ys
  jsonValueToJS (JsonObject x) = jsonObjToJS $ toList x

  jsonObjToJS : List (String, JsonValue) -> JS_IO Ptr
  jsonObjToJS [] =
    jscall "{}" (() -> JS_IO Ptr) ()
  jsonObjToJS ((s,x)::xs) =
    do
      ys <- jsonObjToJS xs
      y <- jsonValueToJS x
      jscall "%2[%0]=%1" (String -> Ptr -> Ptr -> JS_IO Ptr) s y ys
      pure ys

export
encodeJS : (a:SDataTy) -> ISDataTy a -> JS_IO Ptr
encodeJS SString s = pure $ believe_me s
encodeJS SUnit () = jscall "null" (() -> JS_IO Ptr) ()
encodeJS (SList _) [] = jscall "[]" (() -> JS_IO Ptr) ()
encodeJS (SList x) (t::r) =
  do
    z <- encodeJS x t
    w <- encodeJS (SList x) r
    jscall "%1.unshift(%0)" (Ptr -> Ptr -> JS_IO ()) z w
    pure w
encodeJS (STuple x y) (z, w) =
  jscall "[%0,%1]" (Ptr -> Ptr -> JS_IO Ptr) !(encodeJS x z) !(encodeJS y w)
encodeJS (SObj []) [] =
  jscall "{}" (() -> JS_IO Ptr) ()
encodeJS (SObj ((s,x) :: xs)) (MkLabel s v :: r) =
  do
   o <- encodeJS (SObj xs) r
   vv <- encodeJS x v
   jscall "%2[%0]=%1" (String -> Ptr -> Ptr -> JS_IO ()) s vv o
   pure o
--encodeJS (SAlt)
--encodeJS (SEither)
--encodeJS (SMaybe)
encodeJS SJson v = jsonValueToJS v

typeof : Ptr -> JS_IO String
typeof x = jscall "typeof %0" (Ptr -> JS_IO String) x

export
decodeJS : (a:SDataTy) -> Ptr -> JS_IO (Either String (ISDataTy a))
decodeJS SString p =
  do
    t <- typeof p
    if t == "string" then
      pure $ Right $ believe_me p
      else pure $ Left "decodeJS: Not a String"
decodeJS SUnit p =
  do
    isnull <- jscall "(%0 == null)+0" (Ptr -> JS_IO Int) p
    if isnull == 1 then pure $ Right ()
      else pure $ Left "decodeJS: Not null"
decodeJS (SList x) p =
  do
    isArray <- jscall "(Array.isArray(%0))+0" (Ptr -> JS_IO Int) p
    if isArray == 1 then
      do
        len <- jscall "%0.length" (Ptr -> JS_IO Int) p
        if len >0 then
          do
            pfirst <- jscall "%0[0]" (Ptr -> JS_IO Ptr) p
            prest <- jscall "%0.slice(1)" (Ptr -> JS_IO Ptr) p
            first <- decodeJS x pfirst
            rest <- decodeJS (SList x) prest
            pure $ (::) <$> first <*> rest
          else pure $ Right []
      else pure $ Left "decodeJS: Not an Array"
decodeJS (STuple x y) p =
  do
    isArray2 <- jscall "(Array.isArray(%0) && %0.length == 2)+0" (Ptr -> JS_IO Int) p
    if isArray2 == 1 then
      do
        px <- jscall "%0[0]" (Ptr -> JS_IO Ptr) p
        py <- jscall "%0[1]" (Ptr -> JS_IO Ptr) p
        xv <- decodeJS x px
        yv <- decodeJS y py
        pure $ MkPair <$> xv <*> yv
      else pure $ Left "decodeJS: Not a tuple"
decodeJS (SObj []) p = pure $ Right []
decodeJS (SObj ((s,v)::r)) p =
  do
    hasKey <- jscall "(%0 in %1)+0" (String -> Ptr -> JS_IO Int) s p
    if hasKey == 1 then
      do
        pv <- jscall "%0[%1]" (Ptr -> String -> JS_IO Ptr) p s
        vv <- decodeJS v pv
        rv <- decodeJS (SObj r) p
        pure $ (::) <$> (MkLabel s <$> vv) <*> rv
      else pure $ Left $ "decodeJS: missing key" ++ s

mutual

  encodeObjJson : (v: Vect n (String, SDataTy)) -> HVect (SObjTy v) -> SortedMap String JsonValue
  encodeObjJson [] [] = empty
  encodeObjJson ((s,x) :: xs) (MkLabel s v :: r) = insert s (encodeJson x v) $ encodeObjJson xs r

  export
  encodeJson : (a:SDataTy) -> ISDataTy a -> JsonValue
  encodeJson SString s = JsonString s
  encodeJson SUnit () = JsonNull
  encodeJson (SList x) l = JsonArray $ map (encodeJson x) l
  encodeJson (STuple x y) (z, w) = JsonArray [encodeJson x z, encodeJson y w]
  encodeJson (SObj x) y = JsonObject $ encodeObjJson x y
  encodeJson SJson x = x
