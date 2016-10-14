module Js.Json

import public Lightyear
import public Lightyear.Char
import public Lightyear.Strings

import Pruviloj.Core
import public Data.SortedMap

public export
data JsonValue = JsonString String
               | JsonNumber Double
               | JsonBool Bool
               | JsonNull
               | JsonArray (List JsonValue)
               | JsonObject (SortedMap String JsonValue)

{-
export
Eq JsonValue where
  (==) (JsonString x) (JsonString y) = x == y
  (==) (JsonNumber x) (JsonNumber y) = x == y
  (==) JsonNull JsonNull = True
  (==) (JsonArray x) (JsonArray y) = x == y
  (==) (JsonObject x) (JsonObject y) = toList x == toList y
  (==) _ _ = False
-}

export
Show JsonValue where
  show (JsonString s)   = show s
  show (JsonNumber x)   = show x
  show (JsonBool True ) = "true"
  show (JsonBool False) = "false"
  show  JsonNull        = "null"
  show (JsonArray  xs)  = show xs
  show (JsonObject xs)  =
      "{" ++ intercalate ", " (map fmtItem $ SortedMap.toList xs) ++ "}"
    where
      intercalate : String -> List String -> String
      intercalate sep [] = ""
      intercalate sep [x] = x
      intercalate sep (x :: xs) = x ++ sep ++ intercalate sep xs

      fmtItem (k, v) = show k ++ ": " ++ show v

hex : Parser Int
hex = do
  c <- map (ord . toUpper) $ satisfy isHexDigit
  pure $ if c >= ord '0' && c <= ord '9' then c - ord '0'
                                         else 10 + c - ord 'A'

hexQuad : Parser Int
hexQuad = do
  a <- hex
  b <- hex
  c <- hex
  d <- hex
  pure $ a * 4096 + b * 256 + c * 16 + d

specialChar : Parser Char
specialChar = do
  c <- satisfy (const True)
  case c of
    '"'  => pure '"'
    '\\' => pure '\\'
    '/'  => pure '/'
    'b'  => pure '\b'
    'f'  => pure '\f'
    'n'  => pure '\n'
    'r'  => pure '\r'
    't'  => pure '\t'
    'u'  => map chr hexQuad
    _    => fail "expected special char"

jsonString' : Parser (List Char)
jsonString' = (char '"' *!> pure Prelude.List.Nil) <|> do
  c <- satisfy (/= '"')
  if (c == '\\') then map (::) specialChar <*> jsonString'
                 else map (c ::) jsonString'

jsonString : Parser String
jsonString = char '"' *> map pack jsonString' <?> "JSON string"

-- inspired by Haskell's Data.Scientific module
record Scientific where
  constructor MkScientific
  coefficient : Integer
  exponent : Integer

scientificToFloat : Scientific -> Double
scientificToFloat (MkScientific c e) = fromInteger c * exp
  where exp = if e < 0 then 1 / pow 10 (fromIntegerNat (- e))
                       else pow 10 (fromIntegerNat e)

parseScientific : Parser Scientific
parseScientific = do sign <- maybe 1 (const (-1)) `map` opt (char '-')
                     digits <- some digit
                     hasComma <- isJust `map` opt (char '.')
                     decimals <- if hasComma then some digit else pure Prelude.List.Nil
                     hasExponent <- isJust `map` opt (char 'e')
                     exponent <- if hasExponent then integer else pure 0
                     pure $ MkScientific (sign * fromDigits (digits ++ decimals))
                                         (exponent - cast (length decimals))
  where fromDigits : List (Fin 10) -> Integer
        fromDigits = foldl (\a, b => 10 * a + cast b) 0

jsonNumber : Parser Double
jsonNumber = map scientificToFloat parseScientific

jsonBool : Parser Bool
jsonBool  =  (char 't' >! string "rue"  *> pure True)
         <|> (char 'f' >! string "alse" *> pure False) <?> "JSON Bool"

jsonNull : Parser ()
jsonNull = (char 'n' >! string "ull" >! pure ()) <?> "JSON Null"

mutual
  jsonArray : Parser (List JsonValue)
  jsonArray = char '[' *!> (jsonValue `sepBy` (char ',')) <* char ']'

  keyValuePair : Parser (String, JsonValue)
  keyValuePair = do
    key <- spaces *> jsonString <* spaces
    char ':'
    value <- jsonValue
    pure (key, value)

  jsonObject : Parser (SortedMap String JsonValue)
  jsonObject = map fromList (char '{' >! (keyValuePair `sepBy` char ',') <* char '}')

  jsonValue' : Parser JsonValue
  jsonValue' =  (map JsonString jsonString)
            <|> (map JsonNumber jsonNumber)
            <|> (map JsonBool   jsonBool)
            <|> (pure JsonNull <* jsonNull)
            <|>| map JsonArray  jsonArray
            <|>| map JsonObject jsonObject

  jsonValue : Parser JsonValue
  jsonValue = spaces *> jsonValue' <* spaces

jsonToplevelValue : Parser JsonValue
jsonToplevelValue = (map JsonArray jsonArray) <|> (map JsonObject jsonObject)

export
parsJson : String -> Either String JsonValue
parsJson s = parse jsonValue s

public export
interface ToJson a where
  toJson : a -> JsonValue

public export
interface FromJson a where
  fromJson : JsonValue -> Either String a


export
interface (ToJson a, FromJson a) => BothJson a where

export
(ToJson a, FromJson a) => BothJson a where

export
FromJson String where
  fromJson (JsonString s) = Right s
  fromJson o = Left $ "fromJson: " ++ show o ++ " is not a String"

export
ToJson String where
  toJson s = JsonString s

export
FromJson JsonValue where
  fromJson = Right

export
ToJson JsonValue where
  toJson = id

export
FromJson () where
  fromJson JsonNull = Right ()

export
ToJson () where
  toJson () = JsonNull

export
ToJson a => ToJson (List a) where
  toJson x = JsonArray $ map toJson x

export
FromJson a => FromJson (List a) where
  fromJson (JsonArray x) = sequence $ map fromJson x

export
ToJson a => ToJson (Vect n a) where
  toJson x = JsonArray $ toList $ map toJson x

vectFromJson : FromJson a => JsonValue -> Either String (Vect n a)
vectFromJson {n} {a} (JsonArray x) =
  let p1 = the (List (Either String a)) $ map fromJson x
      p2 = sequence $ fromList p1
  in case exactLength n <$> p2 of
        Right (Just z) => Right z

export
FromJson a => FromJson (Vect n a) where
  fromJson = vectFromJson

export
(ToJson a, ToJson b) => ToJson (a,b) where
  toJson (x, y) = JsonArray [toJson x, toJson y]

export
(FromJson a, FromJson b) => FromJson (a, b) where
  fromJson (JsonArray [x, y]) = MkPair <$> fromJson x <*> fromJson y


export
decode : FromJson a => String -> Either String a
decode x = parsJson x >>= fromJson

export
encode : ToJson a => a -> String
encode x = show $ toJson x
