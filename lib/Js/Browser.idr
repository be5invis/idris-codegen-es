module Js.Browser

import public Js.IO

%include js "browser_lib_b.js"

js_create_array : List (JSIO Ptr) -> JSIO Ptr
js_create_array [] = jscall "[]" (JSIO Ptr)
js_create_array (h::r) = do
  ph <- h
  pr <- js_create_array r
  jscall "[%0].concat(%1)" (Ptr -> Ptr -> JSIO Ptr) ph pr

public
const2 : c -> a -> b -> c
const2 x _ _ = x

data Attribute = TextAttribute String String
               | OnEventAttribute String (Ptr -> JSIO ())

record Event where
  constructor MkEvent
  targetValue : String

abstract
data Html : Type -> Type  where 
  HtmlText : String -> Html a
  HtmlNode : String -> List Attribute -> List (String, Event -> a) -> List (Html a) -> Html a
  
public
record App a b where
  constructor MkApp
  state  : b
  view   : b -> Html a
  update : a -> b -> b


public
text : String -> Html a
text x = HtmlText x

public
div : List (Html a) -> Html a
div x = HtmlNode "div" [] [] x

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

setState : b -> JSIO ()
setState z = jscall "b$state = %0" (Ptr -> JSIO ()) (believe_me z)

stepUpdate : App a b -> a -> JSIO ()
stepUpdate ap x = 
  do
    st <- getState
    let new_st = (update ap) x st
    setState new_st
    setDisplay $ view ap new_st
  where
    getState = believe_me <$> jscall "b$state" ( () -> JSIO Ptr) ()

public
runApp : App a b -> JSIO ()
runApp ap =
  do
    setState $ state ap
    setUpdate $ stepUpdate ap
    setDisplay $ view ap $ state ap
  where
    setUpdate : (a -> JSIO ()) -> JSIO ()
    setUpdate z = jscall "b$update = %0" (Ptr -> JSIO ()) (believe_me z)

