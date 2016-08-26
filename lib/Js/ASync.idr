module Js.ASync

%inline
public export
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

export
random : JS_IO Double
random = jscall "Math.random()" (() -> JS_IO Double) ()

export
randomInteger : Integer -> JS_IO Integer
randomInteger x = pure $ cast $ !random * (cast x)

export
randomNat : Nat -> JS_IO Nat
randomNat x = cast <$> randomInteger (cast x)

export
shuffle : List a -> JS_IO (List a)
shuffle x =
  shuffle' x [] (length x)
  where
    shuffle' : List a -> List a -> Nat -> JS_IO (List a)
    shuffle' x r (S i) =
      do
        j <- randomNat (S i)
        let (p, y::s) = splitAt j x
        shuffle' (p++s) (y::r) (i)
    shuffle' _ r Z = pure r

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

export
both : ASync a -> ASync a -> ASync a
both (MkASync s1) (MkASync s2) =
  MkASync $ \onevt =>
    do
      s1 onevt
      s2 onevt

export
data Cursor a = MkCursor (JS_IO ()) ((a -> JS_IO ()) -> JS_IO ())


export
Functor Cursor where
  map f (MkCursor c oe) = MkCursor c (\onevt => oe (\x => onevt (f x)) )


export
newCursor : (JS_IO ()) -> ((a -> JS_IO ()) -> JS_IO ()) -> Cursor a
newCursor c e = MkCursor c e

export
each : (a -> JS_IO ()) -> Cursor a -> JS_IO ()
each proc (MkCursor _ e) = e proc

export
close : Cursor a -> JS_IO ()
close (MkCursor x _) = x
