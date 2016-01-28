module Js.IO

mutual
  public
  data JsTypes : Type -> Type where
    JsInt     : JsTypes Int
    JsString  : JsTypes String
    JsPtr     : JsTypes Ptr
    JsUnit    : JsTypes ()
    JsFun     : JsTypes a -> JsTypes b -> JsTypes (a -> b)
    JsFunIO   : JsTypes a -> JsTypes b -> JsTypes (a -> (IO' FFI_Js) b)

  public
  FFI_Js : FFI
  FFI_Js = MkFFI JsTypes String String

public
JSIO : Type -> Type
JSIO = IO' FFI_Js

%inline
public
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_Js [] ty} -> ty
jscall fname ty = foreign FFI_Js fname ty

public
jsdebug : a -> JSIO ()
jsdebug x = jscall "console.log(%0)" (Ptr -> JSIO ()) (believe_me x)

abstract
data ASync : Type -> Type where
  MkASync : ((a -> JSIO()) -> JSIO ()) -> ASync a

public
setASync : (a -> JSIO ()) -> ASync a -> JSIO ()
setASync onEvent (MkASync set) = set onEvent

public
fireAfter : Int -> a -> ASync a
fireAfter millis x =
  MkASync $ \onevt =>
    jscall  "setTimout(%0, %1)" ((() -> JSIO ()) -> Int -> JSIO ()) (\() => onevt x) millis

public
never : ASync a
never = MkASync (\onevt => pure ())

Functor ASync where
  map f (MkASync oldset) = MkASync (\onevt => oldset (\x => onevt (f x)) )

Applicative ASync where
  pure x = fireAfter 0 x
  (MkASync stepf) <*> (MkASync stepx) =
    MkASync (\onevt => stepf (\f => stepx (\x => onevt (f x)) ))
