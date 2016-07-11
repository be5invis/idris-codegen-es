module Js.BrowserForms

import Debug.Trace

import Js.BrowserBase
import Js.BrowserUtils
import Data.Vect

export
TyError : Type
TyError = List String

export
MError : Type -> Type
MError a = Either TyError a


errors : MError a -> List String
errors (Right _) = []
errors (Left x)  = x

joinMErrors : (a -> b -> c) ->  MError a -> MError b -> MError c
joinMErrors f (Right x) (Right y) = Right $ f x y
joinMErrors _ x         y         = Left $ errors x ++ errors y

export
data Form : Type -> Type where
  MkForm : Typeable a => MError a -> (MError a -> View (MError a)) -> Form a

getFormZ : Form a -> MError a
getFormZ (MkForm x _) = x

getFormV : Form a -> (MError a -> View (MError a))
getFormV (MkForm _ x) = x

public export
data FormUpdate a = ResetForm | FormSetVal a

export
buildForm : Maybe (FormUpdate a) -> Form a -> View a
buildForm {a} x (MkForm s0 f) =
  foldv
    s0
    vw
    update
    ((\y => \_=> g y) <$> x)
  where
    g ResetForm = s0
    g (FormSetVal y) = Right y
    update (Right z) Submit = (s0, Just z)
    update (Left []) Submit = (Left ["Pease fill the form"], Nothing)
    update (Left z) Submit = (Left z, Nothing)
    update _ (Value z) = (z, Nothing)
    vw : MError a -> View (FormEvent (MError a))
    vw z =
      ajaxForm $ (f z) ++ (concat $ map (d . t) $ errors z)

export
buildForm' : Form a -> View a
buildForm' = buildForm Nothing

export
textForm : Form String
textForm =
  MkForm
    (Right "")
    vw
  where
    vw (Right x) = Right <$> (textinput $ Just x)
    vw (Left _) = Right <$> textinput'

export
selectForm : Vect n String -> Form (Fin n)
selectForm lst =
  MkForm
    (Left [])
    (\x => vmap <$> vw x)
  where
    vmap : Fin (S m) -> Either (List String) (Fin m)
    vmap FZ = Left ["Not filled"]
    vmap (FS z) = Right z
    vw (Right x) = selectInput (Just $ FS x) (""::lst)
    vw (Left _) =  selectInput' (""::lst)


export
formBind : (Typeable a, Typeable k) => Form k -> (f : k->Type)
                -> ((x:k) -> Form (f x)) -> ((x:k) -> f x -> a) -> (a->(x:k ** f x)) -> Form a
formBind {a} {k} (MkForm kZ selVw) f kForm kCons getK =
  MkForm
    (kZ >>= makeStart)
    vw
  where
    FoldState : Type
    FoldState = MError (k, MError a)
    makeStart x =
      (\w => kCons x w) <$> getFormZ (kForm x)
    subV : k -> MError a -> View FoldState
    subV x (Left y) = (\w => Right (x, kCons x <$> w)) <$> (getFormV (kForm x) $ Left y)
    subV _ (Right h) =
      let (x ** z) = getK h
      in (\w => Right (x, kCons x <$> w)) <$> (getFormV (kForm x) $ Right z)
    vK : MError k -> View FoldState
    vK x = (\y => (y, Left [])) <$$> selVw x
    foldV : FoldState -> View FoldState
    foldV (Left x) = vK (Left x)
    foldV (Right (x, y)) = vK (Right x) ++ subV x y
    upd : FoldState -> FoldState -> (FoldState, Maybe (MError a))
    upd y x =
      ( x
      , case x of
            Right (_, Right w) => Just $ Right w
            Left e => Just $ Left e
            Right (_, Left e) => Just $ Left e
      )
    theFold : Maybe (FoldState->FoldState) -> View (MError a)
    theFold = foldv ((\x=>(x, Left [])) <$> kZ) foldV upd
    vw : MError a -> View (MError a)
    vw (Left _) = theFold Nothing
    vw (Right x) =
      let (w ** z) = getK x
      in theFold $ Just (\_=> Right (w, Right x))


export
tupleForm : Form a -> Form b -> Form (a,b)
tupleForm {a} {b} (MkForm z1 v1) (MkForm z2 v2) =
  MkForm
    (joinMErrors MkPair z1 z2)
    vw
  where
    FoldState : Type
    FoldState = (MError a, MError b)
    foldVw : FoldState -> View (Either (MError a) (MError b))
    foldVw (x, y) = (Left <$> v1 x) ++ (Right <$> v2 y)
    upd : FoldState -> Either (MError a) (MError b) -> (FoldState, Maybe (MError (a,b)))
    upd (_,z) (Left x) = ((x, z), Just $ joinMErrors MkPair x z)
    upd (z,_) (Right x) = ((z, x), Just $ joinMErrors MkPair z x)
    theFold : Maybe (FoldState->FoldState) -> View (MError (a,b))
    theFold = foldv (z1, z2) foldVw upd
    vw : MError (a,b) -> View (MError (a,b))
    vw (Left _) = theFold Nothing
    vw (Right (x,y)) = theFold (Just $ \_ => (Right x, Right y))

export
formMap : Typeable b => (b->a, a->MError b) -> Form a -> Form b
formMap (f,g) (MkForm z v) =
  MkForm (z >>= g) (\x => g' <$> v (f <$> x))
  where
    g' x = x >>= g

export
formMap' : Typeable b => (b->a, a->b) -> Form a -> Form b
formMap' (f,g) form = formMap (f, \x => Right $ g x) form

export
integerForm : Form Integer
integerForm = formMap' (cast, cast) $ textForm

export
natForm : Form Nat
natForm =
  formMap (cast, i2n) integerForm
  where
    i2n x = if x < 0 then Left [show x ++ "is not a Nat"] else Right $ fromInteger x

export
vtrans : {b : Type} -> ({a:Type} -> View a -> View a) -> Form b -> Form b
vtrans f (MkForm k v) = MkForm k (\x => f $ v x)

export
addSubmit : String -> Form a -> Form a
addSubmit x y = vtrans (\z => z ++ d (submitButton x)) y
