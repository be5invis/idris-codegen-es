module Js.BrowserBase

import Js.IO
import Js.BrowserForeigns
import Control.Arrow
import Data.Vect

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

Eq EventDef where
  (TargetValue x) == (TargetValue y) = x == y

tpathE : (Path->Path) -> EventDef -> EventDef
tpathE f (TargetValue x) = TargetValue $ f x

record Attributes where
  constructor MkAttributes
  value    : String
  class_   : List String
  selected : Bool

emptyAttrs : Attributes
emptyAttrs = MkAttributes "" [] False

data Html : Type where
  HtmlElement : String -> Attributes -> List (String, EventDef) -> Either String (List Html) -> Html

htmlElement : String -> List (String, EventDef) -> List Html -> Html
htmlElement x y z = HtmlElement x emptyAttrs y $ Right z

htmlText : String -> Html
htmlText x = HtmlElement "span" emptyAttrs [] $ Left x

tpath' : (Path->Path) -> Html -> Html
tpath' f (HtmlElement tag attrs events childs) =
  HtmlElement
    tag
    attrs
    (map (\(s, x) => (s, tpathE f x)) events)
    (tpChilds childs)
  where
    tpChilds (Left x) = Left x
    tpChilds (Right x) = Right $ map (tpath' f) x

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

Functor (View c) where
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


attrChangeHtml : (Attributes -> Attributes) -> Html -> Html
attrChangeHtml f (HtmlElement x attrs y z) = HtmlElement x (f attrs) y z

attrChange : (Attributes -> Attributes) -> View a b -> View a b
attrChange f (MkView x r y z) = MkView x ((map $ attrChangeHtml f) . r) y z

-------- view primitives --------

|||Ignores Input, making a view that accepts any input
public
ii : View a b -> View c b
ii (MkView z r ue ui) = MkView z r ue (\x, y => y)

||| Ignores Ouput, making a view that makes no output, hence the outut can have any type needed
public
io : View a b -> View a c
io (MkView z r ue ui) = MkView z r (\x,y => (fst $ ue x y ,Nothing)) ui

public
init : View a b -> a -> View a b
init = flip stepInput

infixl 4 .$. , .?. , <?>

public
(<?>) : (a->Maybe b) -> View c a -> View c b
(<?>) f (MkView z r ue ui) =
  MkView
    z
    r
    updEv
    ui
  where
    updEv x s =
      let (ns, mv) = ue x s
      in (ns, mv >>= f)

public
(.?.) : View b c -> (a-> Maybe b) -> View a c
(.?.) (MkView z r ue ui) f =
  MkView
    z
    r
    ue
    updInput
  where
    updInput x s =
      case f x of
        Just z  => ui z s
        Nothing => s

public
(.$.) : View b c -> (a-> b) -> View a c
(.$.) v f = v .?. (\x => Just $ f x)


infixr 2 .+.

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
(.+.): View a c -> View a c -> View a c
(.+.) x y =
  MkView
  (x,y)
  ovw
  oupdEvt
  (\z,(x,y) => (stepInput z x, stepInput z y))


public
empty : View a b
empty =
  MkView
    ()
    (\x => [])
    (\_, _ => ((), Nothing))
    (\_, _ => ())

public
textinput : View String String
textinput =
  MkView
    ""
    (\x => [ attrChangeHtml (record {value = x}) $ htmlElement "input"  [("change", TargetValue Here)] [] ])
    updEvt
    (\x, y => x)
  where
    updEvt (_,s) y = (s,Just s)


addindex : Vect k a -> Vect k (Fin k, a)
addindex {k} x =
  zip (idx k) x
  where
    idx : (k:Nat) -> Vect k (Fin k)
    idx Z = []
    idx (S i) = FZ :: (map FS $ idx i)

public
selectinput : Vect (S k) String -> View (Fin (S k)) (Fin (S k))
selectinput opts =
  MkView
    FZ
    (render opts)
    updEvt
    updInput
  where
    renderOption : Fin k -> (Fin k, String) -> Html
    renderOption sel (pos, lbl) =
      attrChangeHtml (record {selected = pos == sel, value = show $ finToNat pos}) $ htmlElement
        "option"
        []
        [htmlText lbl]
    render : Vect k String -> Fin k -> List Html
    render opts sel =
      [htmlElement
        "select"
        [("change", TargetValue Here)]
        (toList $ map (renderOption sel) (addindex opts))]
    readSel : (k:Nat) -> String -> Fin (S k)
    readSel u s =
      let i = cast s
      in case integerToFin i (S u) of
            Nothing => FZ
            Just x  => x
    updEvt : Event -> Fin (S k) -> (Fin (S k), Maybe (Fin (S k)))
    updEvt {k} (_,s) _ = let i = readSel k s in (i, Just i)
    updInput x z = x

public
t : String -> View a b
t x =
  MkView
    ()
    (\_ => [htmlText x])
    (\_, _ => ((), Nothing))
    (\_,_ => ())

public
button : b -> String -> View a b
button val lbl =
  MkView
    ()
    render
    updEvt
    (\_, _ => ())
  where
    render () = [htmlElement "button" [("click", TargetValue Here)] [htmlText lbl] ]
    updEvt _ _ = ((), Just val)


public
foldView : (i -> st -> (st, Maybe b)) -> (a -> st -> st) -> st -> View st i -> View a b
foldView onEvt onSet z vw =
  MkView
    (init vw z, z)
    (render . fst)
    updEvt
    (\u, (v, s) => let news = onSet u s in (stepInput news v, news))
  where
    updEvt e (v, s) =
      case stepEvent e v of
        (newv, Nothing) => ((newv, s), Nothing)
        (newv, Just val) => let (news, res) = onEvt val s in ((stepInput news newv, news), res)


groupElement : String -> View a b -> View a b
groupElement tag (MkView z r ue ui) =
  MkView
    z
    (\x => [htmlElement tag [] (r x) ])
    ue
    ui

public
div : View a b -> View a b
div x = groupElement "div" x

public
span : View a b -> View a b
span x = groupElement "span" x

public
dynView : (a->View Void b) -> View a b
dynView rf =
  MkView
    Nothing
    r
    updEvt
    updInp
  where
    r : Maybe (View Void b) -> List Html
    r Nothing = []
    r (Just v) = render v
    updEvt _ Nothing = (Nothing,Nothing)
    updEvt x (Just v) = let (ns, mv) = stepEvent x v in (Just ns, mv)
    updInp x _ = Just $ rf x

public
addClass : String -> View a b -> View a b
addClass classNew = attrChange (\x => record {class_ = classNew :: class_ x } x)
