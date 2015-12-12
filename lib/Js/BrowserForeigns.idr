module Js.BrowserForeigns

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
