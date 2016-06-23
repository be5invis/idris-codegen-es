module Js.BrowserUtils

import Js.BrowserBase
import Js.ASync
import Js.SimpleData

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

public export
data AppGroup : Vect k ((a:Type ** a->Type), Type) -> Type where
  Nil : AppGroup []
  (::) : App a f b -> AppGroup ts -> AppGroup (((a**f), b)::ts)

public export
AppGroupInputTypes : AppGroup ts -> Vect (length ts) Type
AppGroupInputTypes [] = []
AppGroupInputTypes (x::xs) = InputType x :: AppGroupInputTypes xs

public export
AppGroupInputType : AppGroup ts -> Type
AppGroupInputType x =
  Alt (AppGroupInputTypes x)

public export
AppGroupAsyncType : Vect k ((a:Type ** a->Type), Type) -> Type
AppGroupAsyncType ts = Alt (map snd ts)

export
renderAppGroup : (g: AppGroup ts) -> Vect (length ts) (View (AppGroupInputType g))
renderAppGroup [] = []
renderAppGroup (x::xs) = (MkAlt Here <$> renderApp x) :: map (AltExpand<$>) (renderAppGroup xs)

export
stepAppGroupInput : (g: AppGroup ts) -> AppGroupInputType g -> (AppGroup ts, ASync (AppGroupAsyncType ts))
stepAppGroupInput [] y = ([], never)
stepAppGroupInput (x :: z) (MkAlt Here val) =
  let (newApp, async) = stepAppInput x val
  in (newApp :: z, MkAlt Here <$> async)
stepAppGroupInput (x :: z) (MkAlt (There p) val) =
  let (groupRest, async) = stepAppGroupInput z (MkAlt p val)
  in (x :: groupRest, AltExpand <$> async)

export
stepAppGroupAsync : AppGroup ts -> AppGroupAsyncType ts -> (AppGroup ts, ASync (AppGroupAsyncType ts))
stepAppGroupAsync [] _ = ([], never)
stepAppGroupAsync (x :: z) (MkAlt Here val) =
  let (newApp, async) = stepAppASync x val
  in (newApp :: z, MkAlt Here <$> async)
stepAppGroupAsync (x :: z) (MkAlt (There p) val) =
  let (groupRest, async) = stepAppGroupAsync z (MkAlt p val)
  in (x :: groupRest, AltExpand <$> async)
