module Js.Browser

import public Js.IO


removeChild : Ptr -> Int -> JSIO ()
removeChild node pos = jscall "%0.removeChild(%0.childNodes($1) )" (Ptr -> Int -> JSIO ()) node pos

createTextNode : String -> JSIO Ptr
createTextNode s = jscall "document.createTextNode(%0)" (String -> JSIO Ptr) s

appendChild : Ptr -> Ptr -> JSIO ()
appendChild node child = jscall "%0.appendChild(%1)" (Ptr -> Ptr -> JSIO ()) node child

parent : Ptr -> JSIO Ptr
parent node = jscall "%0.parent" (Ptr -> JSIO Ptr) node

body : JSIO Ptr
body = jscall "document.body" (() -> JSIO Ptr) ()

replaceChild : Ptr -> Ptr -> Ptr -> JSIO ()
replaceChild parent new old = jscall "%0.replaceChild(%1, %2)" (Ptr -> Ptr -> Ptr -> JSIO ()) parent new old 

createElement : String -> JSIO Ptr
createElement s = jscall "document.createElement(%0)" (String -> JSIO Ptr) s

setAttribute : Ptr -> (String, String) -> JSIO ()
setAttribute node (k,v) = jscall "%0.setAttribute(%1, %2)" (Ptr -> String -> String -> JSIO ()) node k v


{-
js_create_array : List (JSIO Ptr) -> JSIO Ptr
js_create_array [] = jscall "[]" (JSIO Ptr)
js_create_array (h::r) = do
  ph <- h
  pr <- js_create_array r
  jscall "[%0].concat(%1)" (Ptr -> Ptr -> JSIO Ptr) ph pr

data Attribute = TextAttribute String String
               | OnEventAttribute String (Ptr -> JSIO ())

  -}

data HtmlTree = HtmlText String
              | HtmlContainer String (List (String, String)) (List HtmlTree)

{-
record Event where
  constructor MkEvent
  targetValue : String
  -}

abstract
data View : Type -> Type  where 
  VText  : String -> View a
--  HtmlNode  : String -> List Attribute -> List (String, Event -> a) -> List (Html a) -> Html a

view2htmlTree : View a -> HtmlTree
view2htmlTree (VText s) = HtmlText s

htmltree2js : HtmlTree -> JSIO Ptr
htmltree2js (HtmlText s) = createTextNode s
htmltree2js (HtmlContainer tag attrs childs) =
  do
    node <- createElement tag
    addChilds node childs
    addAttrs node attrs
    return node
  where
    addAttrs : Ptr -> List (String, String) -> JSIO ()
    addAttrs node [] =
      pure ()
    addAttrs node (t::r) =
      do
        setAttribute node t
        addAttrs node r
    addChilds : Ptr -> List HtmlTree -> JSIO ()
    addChilds node [] =
      pure ()
    addChilds node (t::r) =
     do
       c <- htmltree2js t
       appendChild node c
       addChilds node r


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


public
text : String -> View a
text x = VText x

{-
public
div : List (Html a) -> Html a
div x = HtmlNode "div" [] [] x

public
button : a -> Html a -> Html a
button val lbl =
  HtmlNode "button"
           []
           [("onclick", \x => val)]
           [lbl]

public
textinput : Html String
textinput = 
  HtmlNode "input"
           [TextAttribute "type" "text"]
           [("onchange", targetValue)]
           []

callback2attribute : (String, Event -> a) -> Attribute
callback2attribute (n, f)=
  OnEventAttribute n g
  where
    g x = do
      tval <- jscall "%0.target.value" (Ptr -> JSIO String) x
      let msg = f $ MkEvent tval
      upd <- believe_me <$> jscall "b$update" ( () -> JSIO Ptr ) ()
      upd msg


render : Html a -> JSIO Ptr
render (HtmlText s) = jscall "b$node('span', {}, %0)" (String -> JSIO Ptr) s
render (HtmlNode tag attrs callbacks childs) = do
    childs' <- js_create_array $ map render childs
    props' <- mk_props $ attrs ++ map callback2attribute callbacks
    jscall "b$node(%0, %1, %2)" (String -> Ptr -> Ptr -> JSIO Ptr) tag props' childs'
  where
    mk_key_prop : Attribute -> JSIO Ptr
    mk_key_prop (TextAttribute s p) = jscall "[%0, %1]" (String -> String -> JSIO Ptr) s p
    mk_key_prop (OnEventAttribute s p) = jscall "[%0, %1]" (String -> (Ptr -> JSIO ()) -> JSIO Ptr) s p

    mk_props : List Attribute -> JSIO Ptr
    mk_props x = do
      lprops <- (js_create_array $ map mk_key_prop x)
      jscall "b$list2obj(%0)" (Ptr -> JSIO Ptr) lprops


setDisplay : Html a -> JSIO ()
setDisplay e = do
  r <- render e 
  jscall "b$setDisplay(%0)" (Ptr -> JSIO ()) r


stepUpdate : App a b -> a -> JSIO ()
stepUpdate ap x = 
  do
    st <- getState
    let new_st = (update ap) x st
    setState new_st
    setDisplay $ view ap new_st
  where
    getState = believe_me <$> jscall "b$state" ( () -> JSIO Ptr) ()
    -}

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
      diffUpdateTree node ot nt
      diffUpdateChilds node (pos + 1) or nr
  diffUpdateChilds node pos [] (nt::nr) =
    do
      newChild <- htmltree2js nt
      appendChild node newChild
      diffUpdateChilds node pos [] nr

      


  diffUpdateTree : Ptr -> HtmlTree -> HtmlTree -> JSIO ()
  diffUpdateTree node (HtmlContainer oldtag oldAttrs oldChilds) newTree@(HtmlContainer newtag newAttrs newChilds) = 
    if oldtag == newtag then 
      do
        diffUpdateChilds node 0 oldChilds newChilds
      else do
        new <- htmltree2js newTree
        p <- parent node
        replaceChild p node new



updateView : View a -> JSIO ()
updateView z = do
  let newtree = HtmlContainer "div" [("id", "root")] [view2htmlTree z]
  lastTree <- getLastTree
  root <- jscall "document.getElementById('root')" (() -> JSIO Ptr) ()
  diffUpdateTree root lastTree newtree
  setLastTree newtree


public
runApp : App a b -> JSIO ()
runApp ap =
  do
    setState $ state ap
    let v0 = HtmlContainer "div" [("id", "root")] []
    v0d <- htmltree2js v0
    b <- body
    appendChild b v0d
    setLastTree $ v0
    updateView $ view ap $ state ap
    --setUpdate $ stepUpdate ap
    --setDisplay $ view ap $ state ap
--  where
--    setUpdate : (a -> JSIO ()) -> JSIO ()
--    setUpdate z = jscall "b$update = %0" (Ptr -> JSIO ()) (believe_me z)
