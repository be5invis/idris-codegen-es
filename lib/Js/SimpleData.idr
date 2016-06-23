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
{-
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

sStringNotSTuple : (SString = STuple x y) -> Void
sStringNotSTuple Refl impossible

sUnitNotSTuple : (SUnit = STuple x y) -> Void
sUnitNotSTuple Refl impossible

sTuple2Cong : (x, y) = (z, w) -> STuple x y = STuple z w
sTuple2Cong Refl = Refl


sListNotSTuple : (SList x = STuple y z) -> Void
sListNotSTuple Refl impossible

sTupleInjective2 : (STuple x y = STuple z w) -> (x, y) = (z, w)
sTupleInjective2 Refl = Refl


sTupleNotSObj : (STuple x y = SObj xs) -> Void
sTupleNotSObj Refl impossible

sTupleNotSAlt : (STuple x y = SAlt xs) -> Void
sTupleNotSAlt Refl impossible

sStringNotSEither : (SString = SEither x y) -> Void
sStringNotSEither Refl impossible

sStringNotSMaybe : (SString = SMaybe x) -> Void
sStringNotSMaybe Refl impossible

sListNotSEither : (SList x = SEither y z) -> Void
sListNotSEither Refl impossible

sUnitNotSEither : (SUnit = SEither x y) -> Void
sUnitNotSEither Refl impossible

sUnitNotSMaybe : (SUnit = SMaybe x) -> Void
sUnitNotSMaybe Refl impossible

sObjNotSEither : (SObj xs = SEither x y) -> Void
sObjNotSEither Refl impossible

sListNotSMaybe : (SList x = SMaybe y) -> Void
sListNotSMaybe Refl impossible

sTupleNotSEither : (STuple x y = SEither z w) -> Void
sTupleNotSEither Refl impossible

sTupleNotSMaybe : (STuple x y = SMaybe z) -> Void
sTupleNotSMaybe Refl impossible

sObjNotSMaybe : (SObj xs = SMaybe x) -> Void
sObjNotSMaybe Refl impossible

sAltNotSEither : (SAlt xs = SEither x y) -> Void
sAltNotSEither Refl impossible

sAltNotSMaybe : (SAlt xs = SMaybe x) -> Void
sAltNotSMaybe  Refl impossible

export
DecEq SDataTy where
  decEq SString SString = Yes Refl
  decEq SString SUnit = No sStringNotSUnit
  decEq SString (SList x) = No sStringNotSList
  decEq SString (STuple x y) = No sStringNotSTuple
  decEq SString (SObj xs) = No sStringNotSObj
  decEq SString (SAlt xs) = No sStringNotSAlt
  decEq SString (SEither x y) = No sStringNotSEither
  decEq SString (SMaybe x) = No sStringNotSMaybe
  decEq SUnit SString = No $ negEqSym sStringNotSUnit
  decEq SUnit SUnit = Yes Refl
  decEq SUnit (SList x) = No sUnitNotSList
  decEq SUnit (STuple x y) = No sUnitNotSTuple
  decEq SUnit (SObj xs) = No sUnitNotSObj
  decEq SUnit (SAlt xs) = No sUnitNotSAlt
  decEq SUnit (SEither x y) = No sUnitNotSEither
  decEq SUnit (SMaybe x) = No sUnitNotSMaybe
  decEq (SList x) SString = No $ negEqSym sStringNotSList
  decEq (SList x) SUnit = No $ negEqSym sUnitNotSList
  decEq (SList x) (SList y) with (decEq x y)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sListInjective h
  decEq (SList x) (STuple y z) = No sListNotSTuple
  decEq (SList x) (SObj xs) = No sListNotSObj
  decEq (SList x) (SAlt xs) = No sListNotSAlt
  decEq (SList x) (SEither y z) = No sListNotSEither
  decEq (SList x) (SMaybe y) = No sListNotSMaybe
  decEq (STuple x y) SString = No $ negEqSym sStringNotSTuple
  decEq (STuple x y) SUnit = No $ negEqSym sUnitNotSTuple
  decEq (STuple x y) (SList z) = No $ negEqSym sListNotSTuple
  decEq (STuple x y) (STuple z w) with (decEq (x,y) (z,w))
    | Yes p = Yes (sTuple2Cong p)
    | No p = No $ \h => p $ sTupleInjective2 h
  decEq (STuple x y) (SObj xs) = No $ sTupleNotSObj
  decEq (STuple x y) (SAlt xs) = No $ sTupleNotSAlt
  decEq (STuple x y) (SEither z w) = No sTupleNotSEither
  decEq (STuple x y) (SMaybe z) = No sTupleNotSMaybe
  decEq (SObj xs) SString = No $ negEqSym sStringNotSObj
  decEq (SObj xs) SUnit = No $ negEqSym sUnitNotSObj
  decEq (SObj xs) (SList x) = No $ negEqSym sListNotSObj
  decEq (SObj xs) (STuple x y) = No $ negEqSym sTupleNotSObj
  decEq (SObj xs) (SObj ys) with (assert_total $ decEq xs ys )
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sObjInjective h
  decEq (SObj xs) (SAlt ys) = No sObjNotSalt
  decEq (SObj xs) (SEither x y) = No sObjNotSEither
  decEq (SObj xs) (SMaybe x) = No sObjNotSMaybe
  decEq (SAlt xs) SString = No $ negEqSym sStringNotSAlt
  decEq (SAlt xs) SUnit = No $ negEqSym sUnitNotSAlt
  decEq (SAlt xs) (SList x) = No $ negEqSym sListNotSAlt
  decEq (SAlt xs) (STuple x y) = No $ negEqSym sTupleNotSAlt
  decEq (SAlt xs) (SObj ys) = No $ negEqSym sObjNotSalt
  decEq (SAlt xs) (SAlt ys) with (assert_total $ decEq xs ys)
    | Yes p = Yes $ cong p
    | No p = No $ \h => p $ sAltInjective h
  decEq (SAlt xs) (SEither x y) = No sAltNotSEither
  decEq (SAlt xs) (SMaybe x) = No sAltNotSMaybe
  decEq (SEither x y) SString = No $ negEqSym sStringNotSEither
  decEq (SEither x y) SUnit = No $ negEqSym sUnitNotSEither
  decEq (SEither x y) (SList w) = No $ negEqSym sListNotSEither
-}
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
