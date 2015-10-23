module Js.Browser

import public Js.IO


removeChild : Ptr -> Int -> JSIO ()
removeChild node pos = jscall "%0.removeChild(%0.childNodes[%1] )" (Ptr -> Int -> JSIO ()) node pos

childNode : Ptr -> Int -> JSIO Ptr
childNode node pos = jscall "%0.childNodes[%1]" (Ptr -> Int -> JSIO Ptr) node pos

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



record Event where
  constructor MkEvent
  targetValue : String

data HtmlTree : Type where
  HtmlText : String -> List (String, String) -> HtmlTree
  HtmlElement : String -> List (String, String) -> List (String, Event -> JSIO ()) -> (List HtmlTree) -> HtmlTree

abstract
data View : Type -> Type  where 
  VText  : String -> List (String, String) -> View a
  VNode  : String -> List (String, String) -> List (String, Event -> a) -> List (View a) -> View a

evtListen_v2h : (a -> JSIO ()) -> (String, Event -> a) -> (String, Event -> JSIO ())
evtListen_v2h onEvent (s, f) = (s, onEvent . f)

view2htmlTree : (a -> JSIO ()) -> View a -> HtmlTree
view2htmlTree onEvent (VText s attrs) =
  HtmlText s attrs
view2htmlTree onEvent (VNode tag attrs eventListeners childs) =
  HtmlElement tag attrs (map (evtListen_v2h onEvent) eventListeners) (map (view2htmlTree onEvent) childs)

makeEvent : Ptr -> JSIO Event
makeEvent x =
  do
    tv <- jscall "%0.target.value + ''" (Ptr -> JSIO String) x
    pure $ MkEvent tv

evtL2js : (Event -> JSIO ()) -> Ptr -> JSIO ()
evtL2js g x = 
  do
    e <- makeEvent x
    g e

addListeners : Ptr -> List (String, Event -> JSIO ()) -> JSIO ()
addListeners node [] =
  pure ()
addListeners node ((n,f)::r)=
  do
    addEventListener node n (evtL2js f)   

addAttrs : Ptr -> List (String, String) -> JSIO ()
addAttrs node [] =
  pure ()
addAttrs node (t::r) =
  do
    setAttribute node t
    addAttrs node r

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


{-
hmap : (a -> b) -> Html a -> Html b
hmap f (HtmlText s)  = HtmlText s
hmap f x@(HtmlNode s attrs calls childs) = assert_total $
  HtmlNode s
           attrs 
           (map (\(n, g) => (n, f . g )) calls) 
           (map (\x => hmap f x) childs)


instance Functor Html where
  map = hmap

instance Applicative Html where
  pure x = Result x
  f <*> v = case f of
                 Result f' => map f' v
                 Running => Running
                 Error s => Error s
  -}

public
record App a b where
  constructor MkApp
  state  : b
  view   : b -> View a
  update : a -> b -> b


setState : b -> JSIO ()
setState z = jscall "b$state = %0" (Ptr -> JSIO ()) (believe_me z)

setLastTree : HtmlTree -> JSIO ()
setLastTree z = jscall "b$lastView = %0" (Ptr -> JSIO () ) (believe_me z)

getLastTree : JSIO HtmlTree
getLastTree =  believe_me <$> jscall "b$lastView" (() -> JSIO Ptr) ()

mutual
  diffUpdateChilds : Ptr -> Int -> List HtmlTree -> List HtmlTree -> JSIO ()
  diffUpdateChilds node pos [] [] = pure ()
  diffUpdateChilds node pos (ot::or) [] =
    do
      removeChild node pos
      diffUpdateChilds node (pos + 1) or []
  diffUpdateChilds node pos (ot::or) (nt::nr) =
    do
      c <- childNode node pos
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


updateView : View a -> JSIO ()
updateView z =
  do
    let newtree = HtmlElement "div" [("id", "root")] [] [view2htmlTree main_updade z]
    lastTree <- getLastTree
    root <- jscall "document.getElementById('root')" (() -> JSIO Ptr) ()
    diffUpdateTree root lastTree newtree
    setLastTree newtree
  where
    main_updade x =
      do
        upd <- believe_me <$> jscall "b$update" (() -> JSIO ()) ()
        upd x
  

stepUpdate : App a b -> a -> JSIO ()
stepUpdate ap x = 
  do
    st <- getState
    let new_st = (update ap) x st
    setState new_st
    updateView $ view ap new_st
  where
    getState = believe_me <$> jscall "b$state" ( () -> JSIO Ptr) ()

public
runApp : App a b -> JSIO ()
runApp ap =
  do
    setState $ state ap
    let v0 = HtmlElement "div" [("id", "root")] [] []
    v0d <- htmltree2js v0
    b <- body
    appendChild b v0d
    setLastTree $ v0
    setUpdate $ stepUpdate ap
    updateView $ view ap $ state ap
  where
    setUpdate : (a -> JSIO ()) -> JSIO ()
    setUpdate z = jscall "b$update = %0" (Ptr -> JSIO ()) (believe_me z)




-------- view primitives --------

public
text : String -> View a
text x = VText x []

public
div : List (View a) -> View a
div x = VNode "div" [] [] x


public
textinput : View String
textinput = 
  VNode "input"
        [("type", "text")]
        [("change", targetValue)]
        []

{-

public
button : a -> Html a -> Html a
button val lbl =
  HtmlNode "button"
           []
           [("onclick", \x => val)]
           [lbl]


-}

