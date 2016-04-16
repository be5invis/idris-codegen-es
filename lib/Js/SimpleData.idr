module SimpleData

import Data.HVect
import Data.Vect
import Js.ASync

public export
data Label : String -> Type -> Type where
  MkLabel : a -> Label s a

public export
data SDataTy = SString | SList SDataTy | SObj (List (String, SDataTy))

public export
SDataObj : Type
SDataObj = List (String, SDataTy)

public export
total
iSDataTy : SDataTy -> Type
iSDataTy SString = String
iSDataTy (SList x) = List (iSDataTy x)
iSDataTy (SObj x) = assert_total $ HVect $ fromList $ map (iSDataTy . snd) x

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
