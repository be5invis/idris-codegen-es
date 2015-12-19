module Js.BrowserForms

import Js.BrowserBase
import public Js.BrowserUtils

public
TyError : Type
TyError = List String

data FormUpdate a = UpdateValue a
                  | ResetForm

public
data Form : Type -> Type where
  MkForm : (Either TyError a) -> View (FormUpdate a) (Either TyError a) -> Form a

data FormEvent a = FormSetVal (Either TyError a)
                 | FormSubmitVal

FormState : Type -> Type
FormState a = (Either TyError a, Maybe (FormUpdate a))

form_update : Either TyError a -> FormEvent a -> FormState a -> (FormState a, Maybe a)
form_update w (FormSubmitVal) (Right x, _) = ((w, Just ResetForm), Just x)
form_update _ (FormSubmitVal) z@(Left s, _) = (z, Nothing)
form_update _ (FormSetVal x) y = ((x, Nothing) , Nothing)


--foldView : (a -> st -> (st,Maybe res)) -> st -> View st a -> View st res


public
buildForm : Form a -> View a a
buildForm (MkForm z vw) =
  let vw_sub = (FormSetVal <$> vw) ..+. button (FormSubmitVal, "Submit")
      res' = foldView (form_update z) (z, Nothing) (vw_sub .?. snd)
  in res' .$. (\x => (Right x, Just (UpdateValue x)))

--a -> (Either TyError a, FormUpdate a)

-------- form primitives --------
public
textForm : String -> Form String
textForm label =
  MkForm
    (Right "")
    (text label .+.. text ": " .+.. (Right <$> textinput .$. procInput))
  where
    procInput ResetForm = ""
    procInput (UpdateValue x) = x

{-
selectFormAux : String -> List String -> Form (List String)
selectFormAux label opts =
  MkForm
    (div [text label, text ": " , VNode "select" [] [] [map mkopt opts]])
    (childVal 2 $ value)
  where
    mkopt x = VNode "option" [("value", x)] [text x]
-}
{-
public
selectForm : String -> [(String, a)] -> Form (Maybe a)
selectForm label =
  let selectFormAux
-}
