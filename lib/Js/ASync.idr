module Js.ASync

import Data.Vect

%inline
public export
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

export
data Ctx : (b:Type) -> Type where
  MkCtx : Ptr -> Ctx a

export
makeCtx : a -> JS_IO (Ctx a)
makeCtx x = MkCtx <$> jscall "{val: %0}" (Ptr -> JS_IO Ptr) (believe_me x)

export
setCtx : Ctx a -> a -> JS_IO ()
setCtx (MkCtx ctx) z = jscall "%0.val = %1" (Ptr -> Ptr -> JS_IO ()) ctx (believe_me z)

export
getCtx : Ctx a -> JS_IO a
getCtx (MkCtx ctx) = believe_me <$> jscall "%0.val" ( Ptr -> JS_IO Ptr) ctx


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
randomFin : {n: Nat} -> JS_IO (Fin (S n))
randomFin {n} =
  case natToFin !(randomNat (S n)) (S n) of
    Just y => pure y
    Nothing => pure FZ

export total
shuffle : List a -> JS_IO (List a)
shuffle x =
  shuffle' (fromList x) []
  where
    total
    shuffle' : Vect n a -> List a -> JS_IO (List a)
    shuffle' {n = Z} xs ys = pure ys
    shuffle' {n = (S k)} xs ys =
      let pos = !randomFin
      in shuffle' (deleteAt pos xs) (index pos xs :: ys)

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
setTimeout : Int -> a -> ASync a
setTimeout millis x =
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
  pure x = setTimeout 0 x
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
