
module Js.BrowserBase

import Js.BrowserForeigns


data Path = Here
          | PathFst Path
          | PathSnd Path

Eq Path where
  Here        == Here        = True
  (PathFst x) == (PathFst y) = x == y
  (PathSnd x) == (PathSnd y) = x == y
  _           == _           = False

Event : Type
Event = (Path, String)

data EventDef = TargetValue Path
              | FormSubmit Path

Eq EventDef where
  (TargetValue x) == (TargetValue y) = x == y
  (FormSubmit x) == (FormSubmit y) = x == y
  _ == _ = False

tpathE : (Path->Path) -> EventDef -> EventDef
tpathE f (TargetValue x) = TargetValue $ f x
tpathE f (FormSubmit x) = FormSubmit $ f x

record Attributes where
  constructor MkAttributes
  class_   : List String
  selected : Bool
  type     : String

emptyAttrs : Attributes
emptyAttrs = MkAttributes [] False ""

record Html where
  constructor MkHtml
  tag : String
  attrs : Attributes
  eventListeners : List (String, EventDef)
  content : Either String (List Html)
  newVal : Maybe String

htmlElement : String -> List (String, EventDef) -> List Html -> Html
htmlElement x y z = MkHtml x emptyAttrs y (Right z) Nothing

htmlText : String -> Html
htmlText x = MkHtml "span" emptyAttrs [] (Left x) Nothing

total
tpath' : (Path->Path) -> Html -> Html
tpath' f htm =
  record { eventListeners = map (\(s, x) => (s, tpathE f x)) (eventListeners htm)
         , content = assert_total $ tpChilds (content htm)
         } htm
  where
    tpChilds (Left x) = Left x
    tpChilds (Right x) = Right $ map (tpath' f) x

total
tpath : (Path->Path) -> List Html -> List Html
tpath f =  map (tpath' f)

export
data View : Type -> Type where
  MkView : List Html -> (Event -> Maybe a) -> View a

total
getOfTwo : (Event -> Maybe a) -> (Event -> Maybe a) -> Event -> Maybe a
getOfTwo g1 _ (PathFst x, v) = g1 (x,v)
getOfTwo _ g2 (PathSnd x, v) = g2 (x,v)
getOfTwo _ _ (Here,_) = Nothing

export
Semigroup (View a) where
  (MkView h1 g1) <+> (MkView h2 g2) =
      MkView
        (tpath PathFst h1 ++ tpath PathSnd h2)
        (getOfTwo g1 g2)

export
Monoid (View a) where
  neutral =
    MkView
      []
      (\_ => Nothing)

export
record App a b where
  constructor MkApp
  state : b
  render : b -> View a
  update : a -> b -> (b, ASync a)

record AppState a b where
  constructor MkAppState
  theApp : App a b
  theTree : List Html
  getEvt : Event -> Maybe a

createAppState : App a b -> AppState a b
createAppState x =
  let MkView tree f = (render x) (state x)
  in MkAppState x tree f

stepAppState : AppState a b -> a -> (AppState a b, ASync a)
stepAppState apSt x =
  let ap = theApp apSt
      (newS, async) = (update ap) x (state ap)
      MkView tree f = (render ap) newS
  in (record{theApp->state = newS, theTree = tree, getEvt = f} apSt, async)


setAppState : Ptr -> AppState a b -> JS_IO ()
setAppState ctx z = jscall "%0.app = %1" (Ptr -> Ptr -> JS_IO ()) ctx (believe_me z)

getAppState : Ptr -> JS_IO (AppState a b)
getAppState ctx = believe_me <$> jscall "%0.app" ( Ptr -> JS_IO Ptr) ctx

eventDef2JS : (Event -> JS_IO ()) -> EventDef -> Ptr -> JS_IO ()
eventDef2JS procEvt (TargetValue p) evt =
  do
    val <- jscall "%0.target.value" (Ptr-> JS_IO String) evt
    procEvt (p, val)
eventDef2JS procEvt (FormSubmit p) evt =
  do
    jscall "%0.preventDefault()" (Ptr -> JS_IO ()) evt
    procEvt (p, "submit")

addEventListeners : (Event -> JS_IO ()) -> Ptr -> List (String, EventDef) -> JS_IO ()
addEventListeners procEvt node [] =
  pure ()
addEventListeners procEvt node ((e,def)::xs) =
  do
    addEventListener node e (eventDef2JS procEvt def)
    addEventListeners procEvt node xs

classesString : Attributes -> String
classesString x = concat $ intersperse " " $ class_ x

addAttrs : Ptr -> Attributes -> JS_IO ()
addAttrs node attrs =
  do
    setClass node $ classesString attrs
    setSelected node $ selected attrs

sortByKey : Ord a => List (a, b) -> List (a, b)
sortByKey l = sortBy (\(k1,_), (k2,_) => compare k1 k2 ) l

updateAttrs : Ptr -> Attributes -> Attributes -> JS_IO ()
updateAttrs node attrsOld attrsNew =
  do
    updateAttr classesString (setClass node) attrsOld attrsNew
    updateAttr selected (setSelected node) attrsOld attrsNew
  where
    updateAttr : Eq a => (Attributes -> a) -> (a->JS_IO ()) -> Attributes -> Attributes -> JS_IO ()
    updateAttr proj set attrs1 attrs2 =
      if proj attrs1 == proj attrs2 then pure ()
        else set $ proj attrs2


mutual

  addChilds : (Event -> JS_IO ()) -> Ptr -> List Html -> JS_IO ()
  addChilds procEvt node [] =
    pure ()
  addChilds procEvt node (t::r) =
   do
     c <- htmltree2js procEvt t
     appendChild node c
     addChilds procEvt node r

  htmltree2js : (Event -> JS_IO ()) -> Html -> JS_IO Ptr
  htmltree2js procEvt htm =
    do
      node <- createElement (tag htm)
      addChildsAux node (content htm)
      addAttrs node (attrs htm)
      addEventListeners procEvt node (eventListeners htm)
      return node
    where
      addChildsAux : Ptr -> Either String (List Html) -> JS_IO ()
      addChildsAux node (Left x) = setTextContent node x
      addChildsAux  node (Right c) = addChilds procEvt node c

mutual
  diffUpdateChilds : (Event -> JS_IO ()) -> Ptr -> Int -> List Html -> List Html -> JS_IO ()
  diffUpdateChilds procEvt node pos [] [] = pure ()
  diffUpdateChilds procEvt node pos (ot::or) [] =
    do
      removeChild node pos
      diffUpdateChilds procEvt node (pos) or []
  diffUpdateChilds procEvt node pos (ot::or) (nt::nr) =
    do
      c <- childNode pos node
      diffUpdateTree procEvt c ot nt
      diffUpdateChilds procEvt node (pos + 1) or nr
  diffUpdateChilds procEvt node pos [] (nt::nr) =
    do
      newChild <- htmltree2js procEvt nt
      appendChild node newChild
      diffUpdateChilds procEvt node pos [] nr

  refreshNode : (Event -> JS_IO ()) -> Ptr -> Html -> JS_IO ()
  refreshNode procEvt node newNode =
    do
      new <- htmltree2js procEvt newNode
      p <- parent node
      replaceChild p new node


  diffUpdateTree : (Event -> JS_IO ()) -> Ptr -> Html -> Html -> JS_IO ()
  diffUpdateTree procEvt node htmOld htmNew =
    do
     if tag htmOld == tag htmNew && eventListeners htmOld == eventListeners htmNew then
      do
        updateAttrs node (attrs htmOld) (attrs htmNew)
        diffUpdateChildsAux (content htmOld) (content htmNew)
      else refreshNode procEvt node htmNew
     case newVal htmNew of
        Nothing => pure ()
        Just v => setValue node v
    where
      diffUpdateChildsAux : Either String (List Html) -> Either String (List Html) -> JS_IO ()
      diffUpdateChildsAux (Left x) (Left y) =
        if x == y then pure () else setTextContent node y
      diffUpdateChildsAux _ (Left x) =
        setTextContent node x
      diffUpdateChildsAux (Right x) (Right y) =
        diffUpdateChilds procEvt node 0 x y
      diffUpdateChildsAux (Left _) (Right x)=
        addChilds procEvt node x

  updateView : String -> (Event -> JS_IO ()) -> List Html -> List Html -> JS_IO ()
  updateView root procEvt lastTree newtree =
    do
      node <- getElementById root
      diffUpdateChilds procEvt node 0 lastTree newtree

mutual
  makeProcVal : String -> Ptr -> (a: Type) -> Type -> a -> JS_IO ()
  makeProcVal rootName ctx a b val =
    do
      appSt <- the (AppState a b) <$> getAppState ctx
      let (newAppSt, async) = stepAppState appSt val
      updateView rootName (makeProcEvt rootName ctx a b) (theTree appSt) (theTree newAppSt)
      setAppState ctx newAppSt
      setASync (makeProcVal rootName ctx a b) async

  makeProcEvt : String -> Ptr -> Type -> Type -> Event -> JS_IO ()
  makeProcEvt rootName ctx a b evt =
    do
      appSt <- the (AppState a b) <$> getAppState ctx
      case (getEvt appSt) evt of
        Nothing => pure ()
        Just v => makeProcVal rootName ctx a b v

export
runApp : App a b -> JS_IO ()
runApp {a} {b} app =
  do
    let rootName = "root"
    bo <- body
    root <- createElement "div"
    setAttribute root ("id",rootName)
    appendChild bo root
    let appSt = createAppState app
    ctx <- jscall "{}" (() -> JS_IO Ptr) ()
    updateView rootName (makeProcEvt rootName ctx a b) [] (theTree appSt)
    setAppState ctx appSt




----- primitives

export
button : a -> String -> View a
button val lbl =
  MkView
    [htmlElement "button" [("click", TargetValue Here)] [htmlText lbl]]
    (\_ => Just val)

export
text : String -> View a
text s =
  MkView
    [htmlText s]
    (\_=> Nothing)

export
textinput : Maybe String -> View String
textinput v =
  MkView
    [ MkHtml "input" emptyAttrs [("change", TargetValue Here)] (Right []) v ]
    (\(_, x) => Just x)
