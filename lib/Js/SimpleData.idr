module SimpleData

import Data.HVect
import Data.Vect
import Js.IO

public
data Label : String -> Type -> Type where
  MkLabel : a -> Label s a

public
data SDataTy = SString | SList SDataTy | SObj (List (String, SDataTy))

public
SDataObj : Type
SDataObj = List (String, SDataTy)

public
total
iSDataTy : SDataTy -> Type
iSDataTy SString = String
iSDataTy (SList x) = List (iSDataTy x)
iSDataTy (SObj x) = assert_total $ HVect $ fromList $ map (iSDataTy . snd) x

public
total
iSDataObj : SDataObj -> Type
iSDataObj x = iSDataTy $ SObj x

public
encodeJS : (a:SDataTy) -> iSDataTy a -> JSIO Ptr
encodeJS SString s = jscall "%0" (String -> JSIO Ptr) s

public
decodeJS : (a:SDataTy) -> Ptr -> JSIO (Either String (iSDataTy a))
decodeJS SString p =
  do
    c <- jscall "(typeof %0 === 'string')+0" (Ptr -> JSIO Int) p
    if c == 1 then
      Right <$> jscall "%0" (Ptr -> JSIO String) p
      else pure $ Left "decodeVal: Not a String"
