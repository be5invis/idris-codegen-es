module Js.ASync

mutual
  public export
  data JsTypes : Type -> Type where
    JsInt     : JsTypes Int
    JsString  : JsTypes String
    JsPtr     : JsTypes Ptr
    JsUnit    : JsTypes ()
    JsFun     : JsTypes a -> JsTypes b -> JsTypes (a -> b)
    JsFunIO   : JsTypes a -> JsTypes b -> JsTypes (a -> (IO' FFI_Js) b)

  public export
  FFI_Js : FFI
  FFI_Js = MkFFI JsTypes String String

public export
JSIO : Type -> Type
JSIO = IO' FFI_Js

%inline
public export
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_Js [] ty} -> ty
jscall fname ty = foreign FFI_Js fname ty

export
jsdebug : a -> JSIO ()
jsdebug x = jscall "console.log(%0)" (Ptr -> JSIO ()) (believe_me x)

public export
data ASync : Type -> Type where
  MkASync : ((a -> JSIO()) -> JSIO ()) -> ASync a

export
setASync : (a -> JSIO ()) -> ASync a -> JSIO ()
setASync onEvent (MkASync set) = set onEvent

export
total
fireAfter : Int -> a -> ASync a
fireAfter millis x =
  MkASync $ \onevt =>
    jscall  "setTimeout(%0, %1)" ((() -> JSIO ()) -> Int -> JSIO ()) (\() => onevt x) millis

export
never : ASync a
never = MkASync (\onevt => pure ())

export
liftJSIO : JSIO a -> ASync a
liftJSIO x = MkASync (\onevt => x >>= onevt)

export
Functor ASync where
  map f (MkASync oldset) = MkASync (\onevt => oldset (\x => onevt (f x)) )

export
Applicative ASync where
  pure x = fireAfter 0 x
  (MkASync stepf) <*> (MkASync stepx) =
    MkASync (\onevt => stepf (\f => stepx (\x => onevt (f x)) ))

Monad ASync where
  (>>=) (MkASync stepx) f =
    MkASync $ \onevt => stepx (\x => let MkASync stepf = f x in stepf onevt )
