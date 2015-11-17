module Js.Browser

import public Js.IO


removeChild : Ptr -> Int -> JSIO ()
removeChild node pos = jscall "%0.removeChild(%0.childNodes[%1] )" (Ptr -> Int -> JSIO ()) node pos

childNode : Int -> Ptr -> JSIO Ptr
childNode pos node = jscall "%0.childNodes[%1]" (Ptr -> Int -> JSIO Ptr) node pos

createTextNode : String -> JSIO Ptr
createTextNode s = jscall "document.createTextNode(%0)" (String -> JSIO Ptr) s

appendChild : Ptr -> Ptr -> JSIO ()
appendChild node child = jscall "%0.appendChild(%1)" (Ptr -> Ptr -> JSIO ()) node child

parent : Ptr -> JSIO Ptr
parent node = jscall "%0.parentNode" (Ptr -> JSIO Ptr) node

body : JSIO Ptr
body = jscall "document.body" (() -> JSIO Ptr) ()

replaceChild : Ptr -> Ptr -> Ptr -> JSIO ()
replaceChild parent new old = jscall "%0.replaceChild(%1, %2)" (Ptr -> Ptr -> Ptr -> JSIO ()) parent new old

createElement : String -> JSIO Ptr
createElement s = jscall "document.createElement(%0)" (String -> JSIO Ptr) s

setAttribute : Ptr -> (String, String) -> JSIO ()
setAttribute node (k,v) = jscall "%0.setAttribute(%1, %2)" (Ptr -> String -> String -> JSIO ()) node k v

addEventListener : Ptr -> String -> (Ptr -> JSIO ()) -> JSIO ()
addEventListener node evt action = jscall "%0.addEventListener(%1, %2)" (Ptr -> String -> (Ptr -> JSIO ()) -> JSIO ()) node evt action

getElementById : String -> JSIO Ptr
getElementById x = jscall "document.getElementById(%0)" (String -> JSIO Ptr) x

data EventVal a = MkEventVal (Ptr -> JSIO a)

data NodeVal a = MkNodeVal (Ptr -> JSIO a)

instance Functor EventVal where
  map f (MkEventVal ev) = MkEventVal $ \x => f <$> ev x

instance Applicative EventVal where
  pure x = MkEventVal $ \z => pure x
  (MkEventVal f) <*> (MkEventVal x) = MkEventVal $ \z => do
                                                            f' <- f z
                                                            x' <- x z
                                                            pure $ f' x'

value : NodeVal String
value = MkNodeVal $ \x => jscall "%0.value + ''" (Ptr -> JSIO String) x


nodeVal2EventVal : NodeVal a -> EventVal a
nodeVal2EventVal (MkNodeVal f) = MkEventVal $ \z => jscall "%0.target" (Ptr -> JSIO Ptr) z >>= f

targetValue : EventVal String
targetValue = nodeVal2EventVal value --  MkEventVal $ \x => jscall "%0.target.value + ''" (Ptr -> JSIO String) x

parentVal : NodeVal a -> NodeVal a
parentVal (MkNodeVal f) = MkNodeVal $ \x => parent x >>= f

childVal : Int -> NodeVal a -> NodeVal a
childVal pos (MkNodeVal f) = MkNodeVal $ \x => childNode pos x >>= f

data HtmlTree : Type where
  HtmlText : String -> List (String, String) -> HtmlTree
  HtmlElement : String -> List (String, String) -> List (String, Ptr -> JSIO ()) -> (List HtmlTree) -> HtmlTree
  HtmlDynNode : String -> List (String, String) -> List (String, (Ptr -> JSIO ())) ->
                    Ptr -> (Ptr -> HtmlTree) -> (Ptr -> Ptr -> (Ptr, JSIO ()) ) -> HtmlTree

abstract
data View : Type -> Type  where
  VText    : String -> List (String, String) -> View a
  VNode    : String -> List (String, String) -> List (String, EventVal a) -> List (View a) -> View a
  VDynNode : List (String, String) -> List (String, EventVal c) -> b -> (b -> View a) -> (a -> b -> (b, Maybe c)) -> View c

public
noEvents : View a -> View b
noEvents (VText t attrs) = VText t attrs
noEvents (VNode tag attrs _ childs) = VNode tag attrs [] (map noEvents childs)


evtListen_v2h : (a -> JSIO ()) -> (String, EventVal a) -> (String, Ptr -> JSIO ())
evtListen_v2h onEvent (s, MkEventVal f) = (s, \x => do
                                                      z <- f x
                                                      onEvent z
                                           )


addListeners : Ptr -> List (String, Ptr -> JSIO ()) -> JSIO ()
addListeners node [] =
  pure ()
addListeners node ((n,f)::r)=
  do
    addEventListener node n f

addAttrs : Ptr -> List (String, String) -> JSIO ()
addAttrs node [] =
  pure ()
addAttrs node (t::r) =
  do
    setAttribute node t
    addAttrs node r



setState : String -> Ptr -> JSIO ()
setState path z = jscall "b$state[%0] = %1" (String -> Ptr -> JSIO ()) path z

getState : String -> JSIO Ptr
getState path = jscall "b$state[%0]" ( String -> JSIO Ptr) path

setLastTree : String -> HtmlTree -> JSIO ()
setLastTree path z = jscall "b$lastView[%0] = %1" (String -> Ptr -> JSIO () ) path (believe_me z)

getLastTree : String -> JSIO HtmlTree
getLastTree path = believe_me <$> jscall "b$lastView[%0]" ( String -> JSIO Ptr) path


setUpdate : String -> (Ptr -> Ptr -> (Ptr, JSIO ()) ) -> JSIO ()
setUpdate path z = jscall "b$update[%0] = %1" (String -> Ptr -> JSIO ()) path (believe_me z)

getUpdate : String -> JSIO (Ptr -> Ptr -> (Ptr, JSIO ()) )
getUpdate path = believe_me <$> jscall "b$update[%0]" ( String -> JSIO Ptr ) path

setView : String -> (Ptr -> HtmlTree) -> JSIO ()
setView path z = jscall "b$view[%0] = %1" (String -> Ptr -> JSIO ()) path (believe_me z)

getView : String -> JSIO (Ptr -> HtmlTree)
getView path = believe_me <$> jscall "b$view[%0]" ( String -> JSIO Ptr) path

mutual
  addChilds : Ptr -> List HtmlTree -> JSIO ()
  addChilds node [] =
    pure ()
  addChilds node (t::r) =
   do
     c <- htmltree2js t
     appendChild node c
     addChilds node r

  htmltree2js : HtmlTree -> JSIO Ptr
  htmltree2js (HtmlText s attrs) =
    do
      t <- createTextNode s
      node <- createElement "span"
      addAttrs node attrs
      appendChild node t
      return node
  htmltree2js (HtmlElement tag attrs eventListeners childs ) =
    do
      node <- createElement tag
      addChilds node childs
      addAttrs node attrs
      addListeners node eventListeners
      return node
  htmltree2js (HtmlDynNode path attrs eventListeners z vw upd) =
    do
      node <- createElement "span"
      addAttrs node (("id",path)::attrs)
      addListeners node eventListeners
      setState path z
      setView path vw
      setUpdate path upd
      let htm0 = vw z
      v0 <- htmltree2js htm0
      setLastTree path htm0
      appendChild node v0
      return node

maplistener : (a -> b) -> List (String, EventVal a) -> List (String, EventVal b)
maplistener f xs = map (\(n, g) => (n, f <$> g )) xs

hmap : (a -> b) -> View a -> View b
hmap f (VText s attrs)  = VText s attrs
hmap f x@(VNode tag attrs listeners childs) = assert_total $
  VNode tag
    attrs
    (maplistener f listeners)
    (map (\x => hmap f x) childs)
hmap f (VDynNode attrs listeners z vw upd) =
  VDynNode
    attrs
    (maplistener f listeners)
    z
    vw
    (\x,y => let (newSt, mbev) = upd x y in (newSt, map f mbev))

instance Functor View where
  map = hmap

abstract
data ASync : Type -> Type where
  MkASync : ((a -> JSIO()) -> JSIO ()) -> ASync a

setASync : (a -> JSIO ()) -> ASync a -> JSIO ()
setASync onEvent (MkASync set) = set onEvent


public
record App a b where
  constructor MkApp
  state  : b
  view   : b -> View a
  update : a -> b -> (b, Maybe (ASync a))



mutual
  diffUpdateChilds : Ptr -> Int -> List HtmlTree -> List HtmlTree -> JSIO ()
  diffUpdateChilds node pos [] [] = pure ()
  diffUpdateChilds node pos (ot::or) [] =
    do
      removeChild node pos
      diffUpdateChilds node (pos + 1) or []
  diffUpdateChilds node pos (ot::or) (nt::nr) =
    do
      c <- childNode pos node
      diffUpdateTree c ot nt
      diffUpdateChilds node (pos + 1) or nr
  diffUpdateChilds node pos [] (nt::nr) =
    do
      newChild <- htmltree2js nt
      appendChild node newChild
      diffUpdateChilds node pos [] nr




  diffUpdateTree : Ptr -> HtmlTree -> HtmlTree -> JSIO ()
  diffUpdateTree node (HtmlText oldString oldAttrs) newTxt@(HtmlText newString newAttrs) =
    if oldString == newString then
      pure ()
      else do
        new <- htmltree2js newTxt
        p <- parent node
        replaceChild p new node
  diffUpdateTree node (HtmlElement oldtag oldAttrs oldEventListeners oldChilds) newTree@(HtmlElement newtag newAttrs newEventListeners newChilds) =
    if oldtag == newtag then
      do
        diffUpdateChilds node 0 oldChilds newChilds
      else do
        new <- htmltree2js newTree
        p <- parent node
        replaceChild p new node

updateView : String -> HtmlTree -> JSIO ()
updateView path newtree =
  do
    lastTree <- getLastTree path
    node <- getElementById path >>= childNode 0
    diffUpdateTree node lastTree newtree
    setLastTree path newtree

onEvDyn : String -> a -> JSIO ()
onEvDyn path x =
  do
    oldSt <- getState path
    upd <- getUpdate path
    vw <- getView path
    let (newSt, act) = upd (believe_me x) oldSt
    setState path newSt
    updateView path $ vw newSt
    act

mutual
  toHTview : String -> (b -> View a) -> Ptr -> HtmlTree
  toHTview path vw x = view2htmlTree ("0_" ++ path) (onEvDyn path) (vw (believe_me x))

  toHTupd : String -> (c -> JSIO ()) -> (a -> b -> (b, Maybe c)) -> Ptr -> Ptr -> (Ptr, JSIO ())
  toHTupd path onEvent upd x y =
    let (newSt, mbev) = upd (believe_me x) (believe_me y)
        act = case mbev of
                Nothing => pure ()
                Just z  => onEvent z
    in (believe_me newSt, act)

  view2htmlTree : String -> (a -> JSIO ()) -> View a -> HtmlTree
  view2htmlTree path onEvent (VText s attrs) =
    HtmlText s attrs
  view2htmlTree path onEvent (VNode tag attrs eventListeners childs) =
    let evts = map (evtListen_v2h onEvent) eventListeners
        chlds = map (\(i, c) => view2htmlTree (show i ++ "_" ++ path) onEvent c) (zip [1..length childs] childs)
    in HtmlElement tag attrs evts chlds
  view2htmlTree path onEvent (VDynNode attrs eventListeners z vw upd) =
    let evts = map (evtListen_v2h onEvent) eventListeners
    in HtmlDynNode path attrs evts (believe_me z) (toHTview path vw) (toHTupd path onEvent upd)


public
runApp : App a b -> JSIO ()
runApp ap =
  do
    jscall "b$state={}" (() -> JSIO ()) ()
    jscall "b$update={}" (() -> JSIO ()) ()
    jscall "b$view={}" (() -> JSIO ()) ()
    jscall "b$lastView={}" (() -> JSIO ()) ()
    let dynnode = VDynNode [] [] (state ap) (view ap) (update ap)
    let dynhtml = view2htmlTree "0" onNewASync dynnode
    v0 <- htmltree2js dynhtml
    b <- body
    appendChild b v0
  where
    onNewASync : ASync a -> JSIO ()
    onNewASync x = setASync (onEvDyn "0") x


-------- view primitives --------

public
dynamicView : b -> (b -> View a) -> (a -> b -> (b, Maybe c)) -> View c
dynamicView z vw upd = VDynNode [] [] z vw upd

public
text : String -> View a
text x = VText x []

public
div : List (View a) -> View a
div x = VNode "div" [] [] x

public
span : List (View a) -> View a
span x = VNode "span" [] [] x

public
textinput : View String
textinput =
  VNode "input"
        [("type", "text")]
        [("change", targetValue)]
        []

public
button : a -> View a -> View a
button val lbl =
  VNode "button"
    []
    [("click", pure val)]
    [lbl]


-------- forms ------------------
{-}
  VDynNode : List (String, String) -> List (String, EventVal c) -> b -> (b -> View a) -> (a -> b -> (b, Maybe c)) -> View c

abstract
data Form : Type -> Type where
  MkForm : a -> View a -> Form a

data FormEvent a = FormSetVal a
                 | FormSubmitVal

form_update : FormEvent a -> a -> (a, Maybe a)

public
buildForm : Form a -> View a
buildForm (MkForm z vw) =
  let vw_set_val = FormSetVal <$> vw
  in VDynNode
        []
        []
        z
        (\_ => vw_set_val)


  VDynNode [] [] Nothing (\_ => vw) ->

-}
abstract
data Form : Type -> Type where
  MkForm : View a -> NodeVal a -> Form a

public
mkform : Form a -> View a
mkform (MkForm view val) =
  div [ noEvents view
      , VNode "button" [] [("click", nodeVal2EventVal $ parentVal $ childVal 0 $ val)] [text "Submit"]
      ]


-------- form primitives --------
public
textForm : String -> Form String
textForm label =
  MkForm
    (div [ text label, text ": ", VNode "input" [("type","text")] [] [] ])
    (childVal 2 $ value)

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
---------- ASync primitives -----

fireAfter : Int -> a -> ASync a
fireAfter millis x =
  MkASync $ \set =>
    jscall  "setTimout(%0, %1)" ((() -> JSIO ()) -> Int -> JSIO ()) (\() => set x) millis
