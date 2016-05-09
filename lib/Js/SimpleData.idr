module SimpleData

import Data.HVect
import Data.Vect
import Js.ASync

public export
data Label : String -> Type -> Type where
  MkLabel : a -> Label s a

public export
data Alt : Vect n Type -> Type where
  MkAlt : (Elem t ts) -> t -> Alt ts

public export
data SDataTy : Type where
  SString : SDataTy
  SUnit : SDataTy
  SList : SDataTy -> SDataTy
  SObj : List (String, SDataTy) -> SDataTy
  SAlt : List (String, SDataTy) -> SDataTy

sListInjective : SList x = SList y -> x = y
sListInjective Refl = Refl

sObjInjective : SObj x = SObj y -> x = y
sObjInjective Refl = Refl

sAltInjective : SAlt x = SAlt y -> x = y
sAltInjective Refl = Refl

sListNotSObj : (SList x = SObj xs) -> Void
sListNotSObj Refl impossible

sListNotSAlt : (SList x = SAlt xs) -> Void
sListNotSAlt Refl impossible

sObjNotSalt : (SObj xs = SAlt ys) -> Void
sObjNotSalt Refl impossible

sStringNotSUnit : (SString = SUnit) -> Void
sStringNotSUnit Refl impossible

sStringNotSList : (SString = SList x) -> Void
sStringNotSList Refl impossible

sStringNotSObj : (SString = SObj xs) -> Void
sStringNotSObj Refl impossible

sStringNotSAlt : (SString = SAlt xs) -> Void
sStringNotSAlt Refl impossible

sUnitNotSList : (SUnit = SList x) -> Void
sUnitNotSList Refl impossible

sUnitNotSObj : (SUnit = SObj xs) -> Void
sUnitNotSObj Refl impossible

sUnitNotSAlt : (SUnit = SAlt xs) -> Void
sUnitNotSAlt Refl impossible

export
DecEq SDataTy where
  decEq SString SString = Yes Refl
  decEq SString SUnit = No sStringNotSUnit
  decEq SString (SList x) = No sStringNotSList
  decEq SString (SObj xs) = No sStringNotSObj
  decEq SString (SAlt xs) = No sStringNotSAlt
  decEq SUnit SString = No $ negEqSym sStringNotSUnit
  decEq SUnit SUnit = Yes Refl
  decEq SUnit (SList x) = No sUnitNotSList
  decEq SUnit (SObj xs) = No sUnitNotSObj
  decEq SUnit (SAlt xs) = No sUnitNotSAlt
  decEq (SList x) SString = No $ negEqSym sStringNotSList
  decEq (SList x) SUnit = No $ negEqSym sUnitNotSList
  decEq (SList x) (SList y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sListInjective h
  decEq (SList x) (SObj xs) = No sListNotSObj
  decEq (SList x) (SAlt xs) = No sListNotSAlt
  decEq (SObj xs) SString = No $ negEqSym sStringNotSObj
  decEq (SObj xs) SUnit = No $ negEqSym sUnitNotSObj
  decEq (SObj xs) (SList x) = No $ negEqSym sListNotSObj
  decEq (SObj xs) (SObj ys) with (assert_total $ decEq xs ys )
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sObjInjective h
  decEq (SObj xs) (SAlt ys) = No sObjNotSalt
  decEq (SAlt xs) SString = No $ negEqSym sStringNotSAlt
  decEq (SAlt xs) SUnit = No $ negEqSym sUnitNotSAlt
  decEq (SAlt xs) (SList x) = No $ negEqSym sListNotSAlt
  decEq (SAlt xs) (SObj ys) = No $ negEqSym sObjNotSalt
  decEq (SAlt xs) (SAlt ys) with (assert_total $ decEq xs ys)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sAltInjective h

public export
SDataObj : Type
SDataObj = List (String, SDataTy)

public export
total
iSDataTy : SDataTy -> Type
iSDataTy SString = String
iSDataTy SUnit = ()
iSDataTy (SList x) = List (iSDataTy x)
iSDataTy (SObj x) = assert_total $ HVect $ fromList $ map (\z => Label (fst z) (iSDataTy $ snd z) ) x
iSDataTy (SAlt x) = assert_total $ Alt $ fromList $ map (\z => Label (fst z) (iSDataTy $ snd z) ) x


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
