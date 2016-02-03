module Js.BrowserForms

import Js.BrowserBase
import public Js.BrowserUtils
import Data.Vect

public
TyError : Type
TyError = List String

public
MError : Type -> Type
MError a = Either TyError a


data FormUpdate a = UpdateValue a
                  | ResetForm

Functor FormUpdate where
  map f ResetForm = ResetForm
  map f (UpdateValue x) = UpdateValue $ f x

public
data Form : Type -> Type where
  MkForm : MError a -> View (FormUpdate a) (MError a) -> Form a

data FormEvent a = FormSetVal (Either TyError a)
                 | FormSubmitVal

FormState : Type -> Type
FormState a = (MError a, Maybe (FormUpdate a))

form_update : MError a -> FormEvent a -> FormState a -> (FormState a, Maybe a)
form_update w (FormSubmitVal) (Right x, _) =   ((w, Just ResetForm), Just x)
form_update _ (FormSubmitVal) (Left s, _) = ((Left s, Nothing), Nothing)
form_update _ (FormSetVal x) _ = ((x, Nothing) , Nothing)


public
buildForm : Form a -> View a a
buildForm (MkForm z vw) =
  let vw_sub = (FormSetVal <$> vw .?. snd) .+. (button FormSubmitVal "Submit")
  in foldView
        (form_update z)
        (\z, _ => (Right z, Just $ UpdateValue z) )
        (z, Nothing)
        vw_sub


-------- form primitives --------
public
textForm : Form String
textForm =
  MkForm
    (Right "")
    (Right <$> textinput .$. procInput)
  where
    procInput ResetForm = ""
    procInput (UpdateValue x) = x

public
formMap : (b->Maybe a, a->Either TyError b) -> Form a -> Form b
formMap (f,g) (MkForm z vw) =
  MkForm (z >>= g) ( (>>=g) <$> vw .$. onset )
  where
    onset ResetForm = ResetForm
    onset (UpdateValue x) =
      case f x of
        Nothing => ResetForm
        Just z => UpdateValue z

public
formMap' : (b->a, a->b) -> Form a -> Form b
formMap' (f,g) form = formMap (\x => Just $ f x, \x => Right $ g x) form

public
selectForm : Vect (S n) String -> Form (Fin (S n))
selectForm lst =
  MkForm
    (Left ["No value selected"])
    (procEvents <$> selectinput (" "::lst) .$. procInput )
  where
    procInput ResetForm = FZ
    procInput (UpdateValue x) = FS x
    procEvents FZ = Left ["No value selected"]
    procEvents (FS x) = Right x


public
combine : Form k -> (a->k) -> (k->Form a) -> Form a
combine (MkForm kZ selVw) getK kForm =
  MkForm (kZ >>= getZ) ((dynView combineAForm) `chainView` (selVw .$. (getK<$>) ) )
  where
    getZ : k -> MError a
    getZ x = let (MkForm z _) = kForm x in z

    combineAForm : Either (FormUpdate a) (MError k) -> View Void (MError a)
    combineAForm (Right (Right x)) =  let (MkForm _ vw) = kForm x in ii vw
    combineAForm (Left (UpdateValue x) ) =  let (MkForm _ vw) = kForm (getK x) in static vw (UpdateValue x)
    combineAForm _ = empty

--foldView : (i -> st -> (st, Maybe b)) -> (a -> st -> st) -> st -> View st i -> View a b
--MkForm : MError a -> View (FormUpdate a) (MError a) -> Form a

errors : MError a -> List String
errors (Right _) = []
errors (Left x)  = x

joinErrors : MError a -> MError b -> MError (a, b)
joinErrors (Right x) (Right y) = Right (x,y)
joinErrors x         y         = Left $ errors x ++ errors y


public
tupleForm : Form a -> Form b -> Form (a,b)
tupleForm (MkForm xz xvw) (MkForm yz yvw) =
  MkForm
    (joinErrors xz yz)
    (foldView
      updEvt
      updInp
      (xz,yz,Nothing)
      (Left <$> xvw .?. ((fst <$>)<$>) . snd . snd .+. Right <$> yvw .?. ((snd<$>)<$>) . snd . snd )
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
vtrans f (MkForm x v) = MkForm x $ f v

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
