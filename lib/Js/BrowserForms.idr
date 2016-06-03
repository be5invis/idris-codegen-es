module Js.BrowserForms

import Debug.Trace

import Js.BrowserBase
import public Js.BrowserUtils
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

public export
data FormUpdate a = ResetForm | FormSetVal a

export
buildForm : Maybe (FormUpdate a) -> Form a -> View a
buildForm {a} x (MkForm s0 f) =
  foldp
    s0
    vw
    update
    ((\y => \_=> g y) <$> x)
  where
    g ResetForm = s0
    g (FormSetVal y) = Right y
    update Submit (Right z) = (s0, Just z)
    update Submit (Left []) = (Left ["Pease fill the form"], Nothing)
    update Submit (Left z) = (Left z, Nothing)
    update (Value z) _ = (z, Nothing)
    vw : MError a -> View (FormEvent (MError a))
    vw z =
      ajaxForm $ (f z) ++ (concat $ map (div . text) $ errors z)

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
{-


FormState : Type -> Type
FormState a = (a, Bool)

public
data Form : Type -> Type where
  MkForm : a -> View (FormState a) a -> (a -> MError b) -> (b -> a) -> Form b

data FormEvent a = FormSetState a
                 | FormSubmitVal


form_update : a -> (a-> MError b) -> FormEvent a -> FormState a -> (FormState a, Maybe b)
form_update w out (FormSubmitVal) (x, _) =
  case out x of
    Right y => ((w, False), Just y)
    Left e  => ((x, True), Nothing)
form_update _ _ (FormSetState x) (_, s) = ((x, s), Nothing)

renderError : (a -> MError b) -> FormState a -> View Void c
renderError out (x, True) =
  case out x of
    Left errs => concat $ map (div . t) errs
    Right _   => neutral
renderError _ _ = neutral

public
buildForm : Form a -> View a a
buildForm (MkForm z vw out inp) =
  let vw_sub = form FormSubmitVal $ (FormSetState <$> vw)
                <+> (dynView $ renderError out)
                <+> submitButton "Submit"
  in foldView
        (form_update z out)
        (\y, _ => (inp y, False) )
        (z, False)
        vw_sub


-------- form primitives --------
public
textForm : Form String
textForm =
  MkForm
    ""
    (textinput .$. fst)
    Right
    id

public
formMap : (b->a, a->MError b) -> Form a -> Form b
formMap (f,g) (MkForm z vw out inp) =
  MkForm z vw (\x => out x >>= g) (inp . f)

public
formMap' : (b->a, a->b) -> Form a -> Form b
formMap' (f,g) form = formMap (f, \x => Right $ g x) form

public
selectForm : Vect (S n) String -> Form (Fin (S n))
selectForm lst =
  MkForm
    FZ
    (selectinput (" "::lst) .$. fst)
    procEvents
    FS
  where
    procEvents FZ = Left ["No value selected"]
    procEvents (FS x) = Right x


public
combine : Form k -> (a->k) -> (k->Form a) -> Form a
combine (MkForm kZ selVw out inp) getK kForm =
  MkForm
    resetState
    (dynView combineAForm `chainView` (selVw .$. ((fst<$>) . fst))  )
  --MkForm (kZ >>= getZ) ((dynView combineAForm) `chainView` (selVw .$. (getK<$>) ) )
  where
    resetState : MError (k, MError a)
    resetState =
      case kZ of
        (Left e) => Left e
        (Right x) => Right (out x, let MkForm z _ o _ = kForm (out x) in o z)

    combineAForm : Either (MError (k, MError a)) (MError k) -> View Void (MError k, MError a)
    combineAForm (Left s) = neutral
    combineAForm (Right (k ,Left e)) = let (MkForm _ vw _ _) = kForm x in ii ( \x =>  <$> vw)
    combineAForm (Right (Right x)) =  let (MkForm _ vw) = kForm (getK x) in static vw (UpdateValue x)
    --combineAForm (Left (UpdateValue x) ) =  let (MkForm _ vw) = kForm (getK x) in static vw (UpdateValue x)
    --combineAForm (Left ResetForm ) = trace "reseted" $ t "reseted"
    -- let (MkForm _ vw) = kForm (getK x) in static vw (UpdateValue x)

    --combineAForm _ = neutral

--foldView : (i -> st -> (st, Maybe b)) -> (a -> st -> st) -> st -> View st i -> View a b
--MkForm : MError a -> View (FormUpdate a) (MError a) -> Form a




public
tupleForm : Form a -> Form b -> Form (a,b)
tupleForm (MkForm xz xvw) (MkForm yz yvw) =
  MkForm
    (joinMErrors xz yz)
    (foldView
      updEvt
      updInp
      (xz,yz,Nothing)
      ((Left <$> xvw .?. ((fst <$>)<$>) . snd . snd) <+> (Right <$> yvw .?. ((snd<$>)<$>) . snd . snd ))
    )
  where
    updEvt : Either (MError a) (MError b) -> (MError a, MError b, Maybe (FormUpdate (a,b)))
              -> ((MError a, MError b, Maybe (FormUpdate (a,b))), Maybe (MError (a,b)))
    updEvt (Left x) (_, y, _) = ((x, y, Nothing), Just $ joinErrors x y)
    updEvt (Right y) (x, _, _) = ((x, y, Nothing), Just $ joinErrors x y)

    updInp : FormUpdate (a,b) -> (MError a, MError b, Maybe (FormUpdate (a,b)))
              -> (MError a, MError b, Maybe (FormUpdate (a,b)))
    updInp u (x,y,_) = (x,y, Just u)


public
vtrans : {c : Type} -> ({a:Type} -> {b:Type} -> View a b -> View a b) -> Form c -> Form c
vtrans f (MkForm x v o i) = MkForm x (f v) o i

-------- utils ------------
public
integerForm : Form Integer
integerForm = formMap' (cast, cast) $ textForm

public
natForm : Form Nat
natForm =
  formMap (Just . cast, i2n) integerForm
  where
    i2n x = if x < 0 then Left [show x ++ "is not a Nat"] else Right $ fromInteger x
-}
