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


export
data Attribute = CssAttribute String
               | WidthAttribute String
               | HRefAttribute String
               | HiddenAttribute Bool

export
data Event a = EventClick a

export
click : a -> Event a
click = EventClick

export
css : String -> Attribute
css = CssAttribute

export
href : String -> Attribute
href = HRefAttribute

export
hidden : Attribute
hidden = HiddenAttribute True

export
hidden' : Bool -> Attribute
hidden' = HiddenAttribute

export
width : String -> Attribute
width = WidthAttribute

getClass : List Attribute -> List String
getClass (CssAttribute x :: xs) = words x ++ getClass xs
getClass (_::xs) = getClass xs
getClass [] = []

makeClass : List Attribute -> Maybe String
makeClass [] = Nothing
makeClass x = Just $ unwords $ nub $ getClass x

makeWidth : List Attribute -> Maybe String
makeWidth [] = Nothing
makeWidth (WidthAttribute x :: _) = Just x
makeWidth (_::xs) = makeWidth xs

makeHRef : List Attribute -> Maybe String
makeHRef [] = Nothing
makeHRef (HRefAttribute x :: _) = Just x
makeHRef (_::xs) = makeHRef xs

makeHidden : List Attribute -> Maybe String
makeHidden [] = Nothing
makeHidden (HiddenAttribute True :: _) = Just "true"
makeHidden (HiddenAttribute False :: _) = Nothing
makeHidden (_::xs) = makeHidden xs

makeEvents : List (Event a) -> List (String, a)
makeEvents xs =
  nubBy (\(x,_), (y,_) => x == y) (map mkE xs)
  where
    mkE : Event a -> (String, a)
    mkE (EventClick x) = ("click", x)

makeAttributes : List Attribute -> List (String, String)
makeAttributes attrs =
  mkAttr "class" makeClass
  ++ mkAttr "width" makeWidth
  ++ mkAttr "href" makeHRef
  ++ mkAttr "hidden" makeHidden
  where
    mkAttr n m =
      case m attrs of
        Nothing => []
        Just z => [(n, z)]

export
container : String -> List (Event a) -> List Attribute -> View a -> View a
container tag evts attrs child =
  containerNode
    tag
    (makeEvents evts)
    (makeAttributes attrs)
    child


export
idiv : List (Event a) -> List Attribute -> View a -> View a
idiv = container "div"

export
div : List Attribute -> View a -> View a
div = idiv []

export
d : View a -> View a
d x = div [] x

export
ispan : List (Event a) -> List Attribute -> View a -> View a
ispan = container "span"

export
span : List Attribute -> View a -> View a
span = ispan []

export
text : String -> List (Event a) -> List Attribute -> String -> View a
text tag evts attrs txt =
  textNode
    tag
    (makeEvents evts)
    (makeAttributes attrs)
    txt

export
t : String -> View a
t = text "span" [] []

export
link : List Attribute -> String -> View a
link attrs x = text "a" [] attrs x

export
h1 : List Attribute -> String -> View a
h1 attrs x = text "h1" [] attrs x

export
h2 : List Attribute -> String -> View a
h2 attrs x = text "h2" [] attrs x

export
ul : List Attribute -> View a -> View a
ul attrs x = container "ul" [] attrs x

export
li : List Attribute -> View a -> View a
li attrs x = container "ul" [] attrs x

export
textinput : Maybe String -> View String
textinput x = textinputNode "" x

export
textinput' : View String
textinput' = textinput Nothing

export
button : String -> a -> View a
button lbl val = text "button" [click val] [] lbl

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
submitButton x = containerNode "input" [] [("type","submit"),("value",x)] $ empty

export
fileSelector : View (Maybe DomFile)
fileSelector = fileSelectorNode


export
viewBind : Typeable a => View a -> (a -> View b) -> View b
viewBind {a} {b} x f =
  foldv
    Nothing
    render
    upd
    Nothing
  where
    render : Maybe a -> View (Either (Maybe a) b)
    render Nothing = Left <$> (Just <$> x)
    render (Just y) = (Left <$> (Just <$> x)) ++ div [] (Right <$> f y)
    upd : Maybe a -> Either (Maybe a) b -> (Maybe a, Maybe b)
    upd _ (Left z) = (z, Nothing)
    upd _ (Right w) = (Nothing, Just w)
