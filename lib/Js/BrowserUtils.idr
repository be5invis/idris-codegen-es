module Js.BrowserUtils

import Js.BrowserBase
import Js.ASync
import Js.SimpleData
import Data.SortedMap
import Data.SortedSet

infixl 4 <$$>

export
(<$$>) : (Functor m, Functor n) => (a -> b) -> m (n a) -> m (n b)
(<$$>) f x = (f <$>) <$> x

public export
SimpleApp : Type -> Type -> Type
SimpleApp a b = App a (\_=>b) b

export
mkSimpleApp : AppM b a -> (a->View b) -> (a -> b -> AppM b a) -> SimpleApp a b
mkSimpleApp z v u =
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
AppGroupStateTypes : Vect k ((a:Type ** a->Type), Type) -> Vect k Type
AppGroupStateTypes [] = []
AppGroupStateTypes (((x ** _), _)::r) = x :: AppGroupStateTypes r

public export
AppGroupStateType : Vect k ((a:Type ** a->Type), Type) -> Type
AppGroupStateType ts = HVect $ AppGroupStateTypes ts

{-
public export
InputType : App a f b -> a -> Type
InputType {f} app x = f x
-}

public export
AppGroupInputTypes : (ts : Vect k ((a:Type ** a->Type), Type)) -> AppGroupStateType ts -> Vect (length ts) Type
AppGroupInputTypes [] [] = []
AppGroupInputTypes (((x**f),_)::xs) (y::ys) = f y :: AppGroupInputTypes xs ys

public export
AppGroupInputType : (ts : Vect k ((a:Type ** a->Type), Type)) -> AppGroupStateType ts -> Type
AppGroupInputType ts y =
  Alt (AppGroupInputTypes ts y)

{-
public export
AppGroupAsyncType : Vect k ((a:Type ** a->Type), Type) -> Type
AppGroupAsyncType ts = Alt (map snd ts)
-}

export
renderAppGroup : AppGroup ts -> (st : AppGroupStateType ts) -> Vect (length ts) (View (AppGroupInputType ts st))
renderAppGroup [] [] = []
--renderAppGroup (x::xs) = (MkAlt Here <$> renderApp x) :: map (AltExpand<$>) (renderAppGroup xs)
{-
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
getGroupInit : AppGroup ts -> ASync (AppGroupAsyncType ts)
getGroupInit [] = never
getGroupInit (x::xs) = (MkAlt Here <$> getInit x) `both` (AltExpand <$> getGroupInit xs)
-}

public export
data Length = Px Nat

export
Show Length where
  show (Px n) = show n ++ "px"

export
data Attribute = CssAttribute String
               | HRefAttribute String
               | HiddenAttribute Bool
               | StyleAttribute String String
               | IdAttribute String
               | DataAttribute String String

export
data Event a = EventClick a

export
style : String -> String -> Attribute
style k v = StyleAttribute k v

export
width : Length -> Attribute
width x = style "width" (show x)

export
height : Length -> Attribute
height x = style "height" (show x)

export
zindex : Nat -> Attribute
zindex x = style "z-index" (show x)

export
id : String -> Attribute
id x = IdAttribute x

export
click : a -> Event a
click = EventClick

export
css : String -> Attribute
css = CssAttribute

export
dataAttr : String -> String -> Attribute
dataAttr = DataAttribute

export
href : String -> Attribute
href = HRefAttribute

export
hidden : Attribute
hidden = HiddenAttribute True

export
hidden' : Bool -> Attribute
hidden' = HiddenAttribute


makeEvents : List (Event a) -> List (String, a)
makeEvents xs =
  nubBy (\(x,_), (y,_) => x == y) (map mkE xs)
  where
    mkE : Event a -> (String, a)
    mkE (EventClick x) = ("click", x)

makeAttribute : Attribute -> SortedMap String String -> SortedMap String String
makeAttribute (CssAttribute x) y = insert "class" ((lowerMaybe $ lookup "class" y) ++ " " ++ x) y
makeAttribute (HRefAttribute x) y = insert "href" x y
makeAttribute (HiddenAttribute False) y = delete "hidden" y
makeAttribute (HiddenAttribute True) y = insert "hidden" "true" y
makeAttribute (StyleAttribute x y) z = insert "style" ((lowerMaybe $ lookup "style" z) ++ x ++ ":" ++ y ++ ";") z
makeAttribute (IdAttribute x) y = insert "id" x y
makeAttribute (DataAttribute x y) z = insert ("data-" ++ x) y z

makeAttributes : List Attribute -> List (String, String)
makeAttributes attrs = toList $ foldl (flip makeAttribute) empty attrs


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
iimg : List (Event a) -> List Attribute -> String -> View a
iimg evts attrs x = containerNode "img" (makeEvents evts) (("src", x) :: makeAttributes attrs) $ empty

export
img : List Attribute -> String -> View a
img x y = iimg [] x y

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


flexbox : String ->  List (View a ) -> View a
flexbox direction x = div [style "display" "flex", style "flex-direction" direction] $ concat $ map (div []) x

export
flowright : List (View a) -> View a
flowright = flexbox "column"

export
flowdown : List (View a) -> View a
flowdown = flexbox "row"
