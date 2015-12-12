module Js.BrowserBase

import Js.IO
import Js.BrowserForeigns

public
data Path = Here
          | PathFst Path
          | PathSnd Path


Event : Type
Event = (Path, String)

data EventDef = TargetValue Path

tpathE : (Path->Path) -> EventDef -> EventDef
tpathE f (TargetValue x) = TargetValue $ f x

data Html : Type where
  HtmlText : String ->  Html
  HtmlElement : String -> List (String, String) -> List (String, EventDef) -> List Html -> Html

tpath' : (Path->Path) -> Html -> Html
tpath' f (HtmlText x ) =
  HtmlText x
tpath' f (HtmlElement tag attrs events childs) =
  HtmlElement
    tag
    attrs
    (map (\(s, x) => (s, tpathE f x)) events)
    (map (tpath' f) childs)

tpath : (Path->Path) -> List Html -> List Html
tpath f =  map (tpath' f)

abstract
data View : Type -> Type -> Type where
  MkView : d -> (d->List Html) -> (Event->d->(d, Maybe b)) -> (a->d->d) -> View a b


viewMap : (a->b) -> View c a -> View c b
viewMap f (MkView z vw updEvent updInput) =
  MkView
    z
    vw
    (\e, s => let (news, res) = updEvent e s in (news, f <$> res) )
    updInput

instance Functor (View c) where
  map = viewMap

render : View a b -> List Html
render (MkView z vw _ _) = vw z

stepEvent : Event -> View a b -> (View a b, Maybe b)
stepEvent e (MkView z vw upd1 upd2) =
  let (newz, mb) = upd1 e z
  in (MkView newz vw upd1 upd2, mb)

stepInput : a -> View a b -> View a b
stepInput x (MkView z vw upd1 upd2) =
  let newz = upd2 x z
  in MkView newz vw upd1 upd2


idupdEv : a -> s-> (s, Maybe b)
idupdEv x y = (y, Nothing)


staticView : List Html -> View Void b
staticView x = MkView () (\_=>x) idupdEv (\x,y => y)

renderView : a -> (a->List Html) -> View a b
renderView x r =
  MkView
    x
    r
    idupdEv
    (\x,y => x)


public
record App a b where
  constructor MkApp
  state : b
  view : View b a
  update : a -> b -> (b, ASync a)

setApp : App a b -> JSIO ()
setApp z = jscall "b$app = %0" (Ptr -> JSIO ()) (believe_me z)

getApp : JSIO (App a b)
getApp = believe_me <$> jscall "b$app" ( () -> JSIO Ptr) ()

setLastTree : List Html -> JSIO ()
setLastTree z = jscall "b$lastView = %0" (Ptr -> JSIO () ) (believe_me z)

getLastTree : JSIO (List Html)
getLastTree = believe_me <$> jscall "b$lastView" (() -> JSIO Ptr) ()



eventDef2JS : (Event -> JSIO ()) -> EventDef -> Ptr -> JSIO ()
eventDef2JS procEvt (TargetValue p) evt =
  do
    val <- jscall "%0.target.value" (Ptr-> JSIO String) evt
    procEvt (p, val)

addEventListeners : (Event -> JSIO ()) -> Ptr -> List (String, EventDef) -> JSIO ()
addEventListeners procEvt node [] =
  pure ()
addEventListeners procEvt node ((e,def)::xs) =
  do
    addEventListener node e (eventDef2JS procEvt def)
    addEventListeners procEvt node xs

addAttrs : Ptr -> List (String, String) -> JSIO ()
addAttrs node [] =
  pure ()
addAttrs node (t::r) =
  do
    setAttribute node t
    addAttrs node r

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
  htmltree2js procEvt (HtmlText s) = createTextNode s
  htmltree2js procEvt (HtmlElement tag attrs events childs) =
    do
      node <- createElement tag
      addChilds procEvt node childs
      addAttrs node attrs
      addEventListeners procEvt node events
      return node

mutual
  diffUpdateChilds : (Event -> JSIO ()) -> Ptr -> Int -> List Html -> List Html -> JSIO ()
  diffUpdateChilds procEvt node pos [] [] = pure ()
  diffUpdateChilds procEvt node pos (ot::or) [] =
    do
      removeChild node pos
      diffUpdateChilds procEvt node (pos + 1) or []
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
  diffUpdateTree procEvt node (HtmlText oldString) newTxt@(HtmlText newString) =
    if oldString == newString then pure ()
      else refreshNode procEvt node newTxt
{-  diffUpdateTree node (HtmlElement oldtag oldAttrs oldEventListeners oldChilds) newTree@(HtmlElement newtag newAttrs newEventListeners newChilds) =
    do
      eq <- strequals oldEventListeners newEventListeners
      if oldtag == newtag then
        do
          diffUpdateChilds node 0 oldChilds newChilds
        else do
          new <- htmltree2js newTree
          p <- parent node
          replaceChild p new node
-}
  diffUpdateTree procEvt node _ new =
    refreshNode procEvt node new

  updateView : (Event -> JSIO ()) -> List Html -> JSIO ()
  updateView procEvt newtree =
    do
      lastTree <- getLastTree
      node <- getElementById "root"
      diffUpdateChilds procEvt node 0 lastTree newtree
      setLastTree newtree

makeProcEvt : Type -> Type -> Event -> JSIO ()
makeProcEvt t1 t2 evt =
  do
    app <- the (App t1 t2) <$> getApp
    let (MkView z r u1 u2) = view app
    let (afterEvtView, maybeVal) = stepEvent evt $ view app
    case maybeVal of
        Nothing  => refreshApp $ record {view = afterEvtView} app
        Just val => do
          let (newState, act) = update app val $ state app
          let newView = stepInput newState afterEvtView
          refreshApp $ record {state = newState, view = newView} app
  where
    refreshApp : App t1 t2 -> JSIO ()
    refreshApp x =
      do
        setApp x
        updateView (makeProcEvt t1 t2) (render $ view x)

public
runApp : App a b -> JSIO ()
runApp {a} {b} app =
  do
    bo <- body
    root <- createElement "div"
    setAttribute root ("id","root")
    appendChild bo root
    setApp app
    let h = render $ view app
    setLastTree []
    updateView (makeProcEvt a b) h



-------- view primitives --------
infixl 4 .$.

(.$.) : (a->b) -> View b c -> View a c
(.$.) f (MkView z r ue ui) =
  MkView
    z
    r
    ue
    (\x,y => ui (f x) y)

public
ii : View a b -> View c b
ii (MkView z r ue ui) = MkView z r ue (\x, y => y)

infixr 7 .+., ..+., .+.., ..+..

oupdEvt : Event -> (View a c, View b c) -> ((View a c, View b c), Maybe c)
oupdEvt (PathFst z, val) (x, y) =
  let (nx, me) = stepEvent (z,val) x
  in ((nx,y), me)
oupdEvt (PathSnd z, val) (x, y) =
  let (ny, me) = stepEvent (z, val) y
  in ((x,ny), me)

ovw : (View a c, View b c) -> List Html
ovw (x, y) = (tpath PathFst $ render x) ++ (tpath PathSnd $ render y)

public
(..+..): View a c -> View a c -> View a c
(..+..) x y =
  MkView
  (x,y)
  ovw
  oupdEvt
  (\z,(x,y) => (stepInput z x, stepInput z y))

public
(.+.) : View a c -> View b c -> View Void c
(.+.) x y = ii x ..+.. ii y

public
(..+.) : View a c -> View b c -> View a c
(..+.) x y = x ..+.. ii y

public
(.+..) : View a c -> View b c -> View b c
(.+..) x y = ii x ..+.. y


public
textinput : View String String
textinput =
  MkView
    ""
    (\x => [HtmlElement "input" [("value",x)] [("change", TargetValue Here)] [] ])
    updEvt
    (\x, y => x)
  where
    updEvt (_,s) y = (s,Just s)

public
text : String -> View Void b
text x = staticView [HtmlText x]

public
dyntext : View String b
dyntext = renderView "" (\x => [HtmlText x])


public
button : a -> View b a -> View b a
button val lbl =
  MkView
    lbl
    (\x => [HtmlElement "button" [] [("click", TargetValue $ PathSnd Here)] (tpath PathFst $ render x) ])
    updEvt
    stepInput
  where
    updEvt (PathFst x,s) y = let (newst, me) = stepEvent (x,s) y in (newst, me)
    updEvt (PathSnd _, _) y = (y, Just val)

public
foldView : (a -> st -> (st,Maybe res)) -> st -> View st a -> View st res
foldView fold z vw =
  MkView
    (vw, z)
    (render . fst)
    updEvt
    (\s, (v, _) => (stepInput s v, s))
  where
    updEvt e (v, s) =
      case stepEvent e v of
        (newv, Nothing) => ((newv, s), Nothing)
        (newv, Just val) => let (news, r) = fold val s in ((stepInput news newv, news), r)


groupElement : String -> View a b -> View a b
groupElement tag (MkView z r ue ui) =
  MkView
    z
    (\x => [HtmlElement tag [] [] (r x) ])
    ue
    ui

public
div : View a b -> View a b
div x = groupElement "div" x

public
span : View a b -> View a b
span x = groupElement "span" x


--listView : View a b -> View (List a) b
--listView (MkView z r ue ui)
