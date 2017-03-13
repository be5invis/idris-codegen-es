module Js.Typeable

import Pruviloj.Core
import Data.Vect

%language ElabReflection

public export
data TypeRep : Type -> Type where
  TRString : TypeRep String
  TRInteger : TypeRep Integer
  TUnit : TypeRep ()
  TRCons : String -> List String -> (a: Type) -> TypeRep a
  TRCons1 : String -> List String -> (a: Type) -> (f: Type->Type) -> TypeRep a -> TypeRep (f a)
  TRCons2 : String -> List String -> (a: Type) -> (b: Type) -> (f: Type->Type->Type) ->
                TypeRep a -> TypeRep b -> TypeRep (f a b)
  TRCons_Nat : String -> List String -> (f: Nat -> Type) -> (n: Nat) -> TypeRep (f n)
  TRFun : TypeRep a -> TypeRep b -> TypeRep (a -> b)

same : TypeRep a -> TypeRep b -> Bool
same TRString TRString = True
same TRInteger TRInteger = True
same TUnit TUnit = True
same (TRCons x1 y1 _) (TRCons x2 y2 _) = x1 == x2 && y1 == y2
same (TRCons1 x1 y1 _ _ z1) (TRCons1 x2 y2 _ _ z2) = x1 == x2 && y1 == y2 && same z1 z2
same (TRCons2 x1 y1 _ _ _ z1 w1) (TRCons2 x2 y2 _ _ _ z2 w2) = x1 == x2 && y1 == y2 && same z1 z2 && same w1 w2
same (TRCons_Nat x1 y1 _ z1) (TRCons_Nat x2 y2 _ z2) = x1 == x2 && y1 == y2 && z1 == z2
same (TRFun x1 y1) (TRFun x2 y2) = same x1 x2 && same y1 y2
same _ _ = False

export
interface Typeable (a: Type) where
  getTypeRep : TypeRep a

export
tcast : (Typeable a, Typeable b) => a -> Maybe b
tcast {a} {b} x =
  if same (the (TypeRep a) getTypeRep) (the (TypeRep b) getTypeRep) then Just $ believe_me x
    else Nothing

useGetTypeRep : Elab ()
useGetTypeRep =
  do
    [_, s2] <- apply (Var `{getTypeRep}) [True, False]
    solve
    focus s2
    hypothesis

deriveTCons1 : String -> List String -> TTName -> Elab ()
deriveTCons1 name modName x=
  do
    [sub] <- apply `(TRCons1 ~(quote name) ~(quote modName) ~(Var x) ~(Var (NS (UN name) modName))) [False]
    solve
    focus sub
    useGetTypeRep

deriveTCons_Nat : String -> List String -> Elab ()
deriveTCons_Nat name modName =
  do
    [_] <- apply `(TRCons_Nat ~(quote name) ~(quote modName) ~(Var (NS (UN name) modName))) [True]
    solve

deriveTypeableAux : TTName -> TT -> Elab ()
deriveTypeableAux dname val =
  case val of
    P (TCon _ 0) (NS (UN name) modName) _ =>
      do
        fill `(TRCons ~(quote name) ~(quote modName) ~(Var (NS (UN name) modName)))
        solve
    App
      (P (TCon _ 1) (NS (UN name) modName) _)
      (P Bound x _) =>
        deriveTCons1 name modName x <|> deriveTCons_Nat name modName
    App
      (App
        (P (TCon _ 2) (NS (UN name) modName) _)
        (P Bound x _))
      (P Bound y _) =>
        do
          [sub1, sub2] <- apply
                    `(TRCons2 ~(quote name) ~(quote modName) ~(Var x) ~(Var y) ~(Var (NS (UN name) modName)))
                    [False, False]
          solve
          focus sub1
          useGetTypeRep
          focus sub2
          useGetTypeRep
    other => fail [ TermPart other
                  , TextPart "cannot make typeable"
                  ]


export
deriveTypeable : Elab ()
deriveTypeable =
  do
    (ng,tg) <- getGoal
    case tg of
      `(TypeRep ~val) =>
        deriveTypeableAux ng val
      otherGoal => fail [ TermPart otherGoal
                        , TextPart "has an unexpected form for getTypeRep?"
                        ]

export
Typeable String where
  getTypeRep = TRString

export
Typeable Integer where
  getTypeRep = TRInteger

export
(Typeable a, Typeable b) => Typeable (a->b) where
  getTypeRep = TRFun getTypeRep getTypeRep

export
Typeable Bool where
  getTypeRep = %runElab deriveTypeable

export
Typeable () where
  getTypeRep = TUnit

export
Typeable Nat where
  getTypeRep = %runElab deriveTypeable

export
Typeable a => Typeable (Maybe a) where
  getTypeRep = %runElab deriveTypeable

export
Typeable a => Typeable (List a) where
  getTypeRep = %runElab deriveTypeable

export
(Typeable a, Typeable b) => Typeable (Either a b) where
  getTypeRep = %runElab deriveTypeable

export
Typeable (Fin n) where
  getTypeRep = %runElab deriveTypeable

export
(Typeable a, Typeable b) => Typeable (a, b) where
  getTypeRep = %runElab deriveTypeable
