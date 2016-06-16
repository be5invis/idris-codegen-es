module Js.BrowserUtils

import Js.BrowserBase

infixl 4 <$$>

export
(<$$>) : (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) f x = (f <$>) <$> x

export
div : View a -> View a
div x = ContainerNode "div" [] [] x

export
button : String -> a -> View a
button lbl val = ContainerNode "button" [("click", Just val)] [] $ text lbl

export
selectInput : Maybe (Fin n) -> Vect n String -> View (Fin n)
selectInput f o = SelectNode f o

export
selectInput' : Vect n String -> View (Fin n)
selectInput' o = selectInput Nothing o

export
ajaxForm : View a -> View (FormEvent a)
ajaxForm x = AjaxFormNode x

export
submitButton : String -> View a
submitButton x = ContainerNode "input" [] [("type","submit"),("value",x)] $ text ""
