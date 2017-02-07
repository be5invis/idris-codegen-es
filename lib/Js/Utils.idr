module Utils

import public Data.Vect

public export
Nil : Fin 0 -> a
Nil FZ impossible
Nil (FS _) impossible

public export
(::) : a -> (Fin n -> a) -> Fin (S n) -> a
(::) x f (FS k) = f k
(::) x f FZ = x

%inline
public export
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_JS [] ty} -> ty
jscall fname ty = foreign FFI_JS fname ty

export
debugError : String -> JS_IO a
debugError s = believe_me <$> jscall "throw2(%0)" (String -> JS_IO ()) s

export
setTimeout : JS_IO () -> Int -> JS_IO ()
setTimeout act millis = jscall "setTimeout(%0,%1)" (JsFn (() -> JS_IO ()) -> Int -> JS_IO ()) (MkJsFn (\()=>act)) millis

export
isUndefined : Ptr -> JS_IO Bool
isUndefined x =
  do
    i <- jscall "(%0 == undefined)+0" (Ptr -> JS_IO Int) x
    if i == 0 then
      pure False
      else pure True


export
data JSIORef : (b:Type) -> Type where
  MkJSIORef : Ptr -> JSIORef a

export
newJSIORef : a -> JS_IO (JSIORef a)
newJSIORef x = MkJSIORef <$> jscall "{val: %0}" (Ptr -> JS_IO Ptr) (believe_me x)

export
writeJSIORef : JSIORef a -> a -> JS_IO ()
writeJSIORef (MkJSIORef ctx) z = jscall "%0.val = %1" (Ptr -> Ptr -> JS_IO ()) ctx (believe_me z)

export
readJSIORef : JSIORef a -> JS_IO a
readJSIORef (MkJSIORef ctx) = believe_me <$> jscall "%0.val" ( Ptr -> JS_IO Ptr) ctx

export
modifyJSIORef : JSIORef a -> (a->a) -> JS_IO ()
modifyJSIORef ref f =
  do
    v <- readJSIORef ref
    writeJSIORef ref (f v)

export
random : JS_IO Double
random = jscall "Math.random()" (() -> JS_IO Double) ()

export
randomInt : Int -> JS_IO Int
randomInt x = pure $ cast $ !random * (cast x)

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

export
readJSList : Ptr -> JS_IO (List Ptr)
readJSList x =
  do
    len <- jscall "%0.length" (Ptr -> JS_IO Int) x
    if len > 0 then
      do
        pfirst <- jscall "%0[0]" (Ptr -> JS_IO Ptr) x
        prest <- jscall "%0.slice(1)" (Ptr -> JS_IO Ptr) x
        rest <- readJSList prest
        pure $ pfirst :: rest
      else
          pure []

export
makeJSList : List Ptr -> JS_IO Ptr
makeJSList [] = jscall "[]" (() -> JS_IO Ptr) ()
makeJSList (x::xs) =
  do
    res <- makeJSList xs
    jscall "%1.unshift(%0)" (Ptr -> Ptr -> JS_IO ()) x res
    pure res

export
makeJSObj : List (String, Ptr) -> JS_IO Ptr
makeJSObj [] =
  jscall "{}" (() -> JS_IO Ptr) ()
makeJSObj ((k,v)::xs) =
  do
    o <- makeJSObj xs
    jscall "%2[%0]=%1" (String -> Ptr -> Ptr -> JS_IO ()) k v o
    pure o

export
makeJSStringObj : List (String, String) -> JS_IO Ptr
makeJSStringObj xs = makeJSObj $ map (\(x,y)=>(x,believe_me y)) xs
