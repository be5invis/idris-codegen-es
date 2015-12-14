module Js.BrowserForms

import Js.BrowserBase
import public Js.BrowserUtils

public
TyError : Type
TyError = List String


abstract
data Form : Type -> Type where
  MkForm : (Either TyError a) -> View () (Either TyError a) -> Form a

data FormEvent a = FormSetVal a
                 | FormSubmitVal

form_update : FormEvent (Either TyError a) -> Either TyError a -> (Either TyError a, Maybe a)
form_update (FormSubmitVal) z@(Right x) = (z, Just x)
form_update (FormSubmitVal) z@(Left s) = (z, Nothing)
form_update (FormSetVal x) y = (x, Nothing)


public
buildForm : Form a -> View Void a
buildForm (MkForm z vw) =
  let vw_sub = (FormSetVal <$> vw) .+. button (FormSubmitVal, "Submit")
  in ii $ foldView form_update z (ii vw_sub)



-------- form primitives --------
public
textForm : String -> Form String
textForm label =
  MkForm
    (Right "")
    (ii $ text label .+. text ": " .+.. (Right <$> textinput))

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
