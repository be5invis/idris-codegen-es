module Js.BrowserUtils

import Js.BrowserBase
import Js.ASync

infixl 4 <$$>

export
(<$$>) : (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) f x = (f <$>) <$> x

public export
SimpleApp : Type -> Type -> Type
SimpleApp a b = App a (\_=>b) b

export
MkSimpleApp : a -> (a->View b) -> (a -> b -> (a,ASync b)) -> SimpleApp a b
MkSimpleApp z v u =
  MkApp
    z
    v
    u
    u

export
div : View a -> View a
div x = containerNode "div" [] [] x

export
text : String -> View a
text s = textNode s

export
t : String -> View a
t = text

export
textinput : Maybe String -> View String
textinput x = inputNode x

export
textinput' : View String
textinput' = textinput Nothing

export
button : String -> a -> View a
button lbl val = containerNode "button" [("click", Just val)] [] $ text lbl

export
selectInput : Maybe (Fin n) -> Vect n String -> View (Fin n)
selectInput f o = selectNode f o

export
selectInput' : Vect n String -> View (Fin n)
selectInput' o = selectInput Nothing o

export
ajaxForm : View a -> View (FormEvent a)
ajaxForm x = ajaxFormNode x

export
submitButton : String -> View a
submitButton x = containerNode "input" [] [("type","submit"),("value",x)] $ text ""
