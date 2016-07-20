module Js.ASync

%inline
public export
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

public export
data ASync : Type -> Type where
  MkASync : ((a -> JS_IO()) -> JS_IO ()) -> ASync a

export
setASync : (a -> JS_IO ()) -> ASync a -> JS_IO ()
setASync onEvent (MkASync set) =
  do
    set onEvent
    pure ()

export
total
fireAfter : Int -> a -> ASync a
fireAfter millis x =
  MkASync $ \onevt => assert_total $
    jscall  "setTimeout(%0, %1)" ( JsFn (() -> JS_IO ()) -> Int -> JS_IO ()) (MkJsFn $ \() => onevt x) millis

export
never : ASync a
never = MkASync (\onevt => pure ())

export
error : String -> ASync a
error s = MkASync (\_ => jscall "throw2(%0)" (String -> JS_IO ()) s)

export
liftJS_IO : JS_IO a -> ASync a
liftJS_IO x = MkASync (\onevt => x >>= onevt)

export
Functor ASync where
  map f (MkASync oldset) = MkASync (\onevt => oldset (\x => onevt (f x)) )

export
Applicative ASync where
  pure x = fireAfter 0 x
  (MkASync stepf) <*> (MkASync stepx) =
    MkASync (\onevt => stepf (\f => stepx (\x => onevt (f x)) ))

export
Monad ASync where
  (>>=) (MkASync stepx) f =
    MkASync $ \onevt => stepx (\x => let MkASync stepf = f x in stepf onevt )
