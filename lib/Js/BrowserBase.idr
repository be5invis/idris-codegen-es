
module Js.BrowserBase

import Js.IO
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
  value    : String
  class_   : List String
  selected : Bool
  type     : String

emptyAttrs : Attributes
emptyAttrs = MkAttributes "" [] False ""

data Html : Type where
  HtmlElement : String -> Attributes -> List (String, EventDef) -> Either String (List Html) -> Html

htmlElement : String -> List (String, EventDef) -> List Html -> Html
htmlElement x y z = HtmlElement x emptyAttrs y $ Right z

htmlText : String -> Html
htmlText x = HtmlElement "span" emptyAttrs [] $ Left x

total
tpath' : (Path->Path) -> Html -> Html
tpath' f (HtmlElement tag attrs events childs) =
  HtmlElement
    tag
    attrs
    (map (\(s, x) => (s, tpathE f x)) events)
    (assert_total $ tpChilds childs)
  where
    tpChilds (Left x) = Left x
    tpChilds (Right x) = Right $ map (tpath' f) x

total
tpath : (Path->Path) -> List Html -> List Html
tpath f =  map (tpath' f)

abstract
data View : Type -> Type where
  MkView : List Html -> (Event -> Maybe a) -> View a

total
getOfTwo : (Event -> Maybe a) -> (Event -> Maybe a) -> Event -> Maybe a
getOfTwo g1 _ (PathFst x, v) = g1 (x,v)
getOfTwo _ g2 (PathSnd x, v) = g2 (x,v)
getOfTwo _ _ (Here,_) = Nothing

Semigroup (View a) where
  (MkView h1 g1) <+> (MkView h2 g2) =
      MkView
        (tpath PathFst h1 ++ tpath PathSnd h2)
        (getOfTwo g1 g2)

Monoid (View a) where
  neutral =
    MkView
      []
      (\_ => Nothing)

public
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


setAppState : Ptr -> AppState a b -> JSIO ()
setAppState ctx z = jscall "%0.app = %1" (Ptr -> Ptr -> JSIO ()) ctx (believe_me z)

getAppState : Ptr -> JSIO (AppState a b)
getAppState ctx = believe_me <$> jscall "%0.app" ( Ptr -> JSIO Ptr) ctx

eventDef2JS : (Event -> JSIO ()) -> EventDef -> Ptr -> JSIO ()
eventDef2JS procEvt (TargetValue p) evt =
  do
    val <- jscall "%0.target.value" (Ptr-> JSIO String) evt
    procEvt (p, val)
eventDef2JS procEvt (FormSubmit p) evt =
  do
    jscall "%0.preventDefault()" (Ptr -> JSIO ()) evt
    procEvt (p, "submit")

addEventListeners : (Event -> JSIO ()) -> Ptr -> List (String, EventDef) -> JSIO ()
addEventListeners procEvt node [] =
  pure ()
addEventListeners procEvt node ((e,def)::xs) =
  do
    addEventListener node e (eventDef2JS procEvt def)
    addEventListeners procEvt node xs

classesString : Attributes -> String
classesString x = concat $ intersperse " " $ class_ x

addAttrs : Ptr -> Attributes -> JSIO ()
addAttrs node attrs =
  do
    setValue node $ value attrs
    setClass node $ classesString attrs
    setSelected node $ selected attrs

sortByKey : Ord a => List (a, b) -> List (a, b)
sortByKey l = sortBy (\(k1,_), (k2,_) => compare k1 k2 ) l

updateAttrs : Ptr -> Attributes -> Attributes -> JSIO ()
updateAttrs node attrsOld attrsNew =
  do
    updateAttr value (setValue node) attrsOld attrsNew
    updateAttr classesString (setClass node) attrsOld attrsNew
    updateAttr selected (setSelected node) attrsOld attrsNew
  where
    updateAttr : Eq a => (Attributes -> a) -> (a->JSIO ()) -> Attributes -> Attributes -> JSIO ()
    updateAttr proj set attrs1 attrs2 =
      if proj attrs1 == proj attrs2 then pure ()
        else set $ proj attrs2


mutual

  addChilds : (Event -> JSIO ()) -> Ptr -> List Html -> JSIO ()
  addChilds procEvt node [] =
    pure ()
  addChilds procEvt node (t::r) =
   do
     c <- htmltree2js procEvt t
     appendChild node c
     addChilds procEvt node r

  htmltree2js : (Event -> JSIO ()) -> Html -> JSIO Ptr
  htmltree2js procEvt (HtmlElement tag attrs events childs) =
    do
      node <- createElement tag
      addChildsAux node childs
      addAttrs node attrs
      addEventListeners procEvt node events
      return node
    where
      addChildsAux : Ptr -> Either String (List Html) -> JSIO ()
      addChildsAux node (Left x) = setTextContent node x
      addChildsAux  node (Right c) = addChilds procEvt node c

mutual
  diffUpdateChilds : (Event -> JSIO ()) -> Ptr -> Int -> List Html -> List Html -> JSIO ()
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

  refreshNode : (Event -> JSIO ()) -> Ptr -> Html -> JSIO ()
  refreshNode procEvt node newNode =
    do
      new <- htmltree2js procEvt newNode
      p <- parent node
      replaceChild p new node


  diffUpdateTree : (Event -> JSIO ()) -> Ptr -> Html -> Html -> JSIO ()
  diffUpdateTree procEvt node (HtmlElement oldtag oldAttrs oldEventListeners oldChilds)
                      new@(HtmlElement newtag newAttrs newEventListeners newChilds) =
     if oldtag == newtag && oldEventListeners == newEventListeners then
      do
        updateAttrs node oldAttrs newAttrs
        diffUpdateChildsAux oldChilds newChilds
      else refreshNode procEvt node new
     where
      diffUpdateChildsAux : Either String (List Html) -> Either String (List Html) -> JSIO ()
      diffUpdateChildsAux (Left x) (Left y) =
        if x == y then pure () else setTextContent node y
      diffUpdateChildsAux _ (Left x) =
        setTextContent node x
      diffUpdateChildsAux (Right x) (Right y) =
        diffUpdateChilds procEvt node 0 x y
      diffUpdateChildsAux (Left _) (Right x)=
        addChilds procEvt node x

  updateView : String -> (Event -> JSIO ()) -> List Html -> List Html -> JSIO ()
  updateView root procEvt lastTree newtree =
    do
      node <- getElementById root
      diffUpdateChilds procEvt node 0 lastTree newtree

mutual
  makeProcVal : String -> Ptr -> (a: Type) -> Type -> a -> JSIO ()
  makeProcVal rootName ctx a b val =
    do
      appSt <- the (AppState a b) <$> getAppState ctx
      let (newAppSt, async) = stepAppState appSt val
      updateView rootName (makeProcEvt rootName ctx a b) (theTree appSt) (theTree newAppSt)
      setAppState ctx newAppSt
      setASync (makeProcVal rootName ctx a b) async

  makeProcEvt : String -> Ptr -> Type -> Type -> Event -> JSIO ()
  makeProcEvt rootName ctx a b evt =
    do
      appSt <- the (AppState a b) <$> getAppState ctx
      case (getEvt appSt) evt of
        Nothing => pure ()
        Just v => makeProcVal rootName ctx a b v

public
runApp : App a b -> JSIO ()
runApp {a} {b} app =
  do
    let rootName = "root"
    bo <- body
    root <- createElement "div"
    setAttribute root ("id",rootName)
    appendChild bo root
    let appSt = createAppState app
    ctx <- jscall "{}" (() -> JSIO Ptr) ()
    --let newView = stepInput (state app) (view app)
    --let newApp = record {view = newView} app
    --setApp newApp
    --let h = render $ view newApp
    --setLastTree []
    updateView rootName (makeProcEvt rootName ctx a b) [] (theTree appSt)
    setAppState ctx appSt




----- primitives

public
button : a -> String -> View a
button val lbl =
  MkView
    [htmlElement "button" [("click", TargetValue Here)] [htmlText lbl]]
    (\_ => Just val)

public
text : String -> View a
text s =
  MkView
    [htmlText s]
    (\_=> Nothing)

public
textinput : View String
textinput =
  MkView
    [ htmlElement "input"  [("change", TargetValue Here)] [] ]
    (\(_, x) => Just x)
