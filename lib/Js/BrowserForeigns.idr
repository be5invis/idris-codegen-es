module Js.BrowserForeigns

import public Js.ASync

%access export

lenChilds : Ptr -> JS_IO Int
lenChilds node = jscall "%0.removeChild(%0.childNodes.length)" (Ptr -> JS_IO Int) node

removeChild : Ptr -> Int -> JS_IO ()
removeChild node pos = jscall "%0.removeChild(%0.childNodes[%1] )" (Ptr -> Int -> JS_IO ()) node pos

childNode : Int -> Ptr -> JS_IO Ptr
childNode pos node = jscall "%0.childNodes[%1]" (Ptr -> Int -> JS_IO Ptr) node pos


setTextContent : Ptr -> String -> JS_IO ()
setTextContent node s = jscall "%0.textContent = %1" (Ptr -> String -> JS_IO ()) node s

appendChild : Ptr -> Ptr -> JS_IO Ptr
appendChild node child = jscall "%0.appendChild(%1)" (Ptr -> Ptr -> JS_IO Ptr) node child

parent : Ptr -> JS_IO Ptr
parent node = jscall "%0.parentNode" (Ptr -> JS_IO Ptr) node

docBody : JS_IO Ptr
docBody = jscall "document.body" (() -> JS_IO Ptr) ()

replaceChild : Ptr -> Ptr -> Ptr -> JS_IO ()
replaceChild parent new old = jscall "%0.replaceChild(%1, %2)" (Ptr -> Ptr -> Ptr -> JS_IO ()) parent new old

createElement : String -> JS_IO Ptr
createElement s = jscall "document.createElement(%0)" (String -> JS_IO Ptr) s

setAttribute : Ptr -> (String, String) -> JS_IO ()
setAttribute node (k,v) = jscall "%0.setAttribute(%1, %2)" (Ptr -> String -> String -> JS_IO ()) node k v

removeAttribute : Ptr -> String -> JS_IO ()
removeAttribute node k = jscall "%0.removeAttribute(%1)" (Ptr -> String -> JS_IO ()) node k

addEventListener : Ptr -> String -> (Ptr -> JS_IO ()) -> JS_IO ()
addEventListener node evt action =
  jscall
    "%0.addEventListener(%1, %2)"
    (Ptr -> String -> (JsFn (Ptr -> JS_IO ())) -> JS_IO ())
    node
    evt
    (MkJsFn action)

getElementById : String -> JS_IO Ptr
getElementById x = jscall "document.getElementById(%0)" (String -> JS_IO Ptr) x

setValue : Ptr -> String -> JS_IO ()
setValue node val = jscall "%0.value = %1" (Ptr->String->JS_IO ()) node val

setClass : Ptr -> String -> JS_IO ()
setClass node val = jscall "%0.className = %1" (Ptr->String->JS_IO ()) node val

setSelected : Ptr -> Bool -> JS_IO ()
setSelected node True = jscall "%0.selected = true" (Ptr->JS_IO ()) node
setSelected node False = jscall "%0.selected = false" (Ptr->JS_IO ()) node



------ Network -------

httpGet_raw : String -> (String -> JS_IO ()) -> JS_IO ()
httpGet_raw url callback =
  jscall
    ("function(){var xmlhttp=new XMLHttpRequest();console.log(%0);"++
    "xmlhttp.onreadystatechange=function(){if(xmlhttp.readyState==4){"++
    "if(xmlhttp.status==200){console.log(xmlhttp.responseText);%1(xmlhttp.responseText)}} };"++
    "xmlhttp.open('GET',%0, true);"++
    "xmlhttp.send(null);}()")
    (String -> (JsFn (String -> JS_IO ())) -> JS_IO ())
    url
    (MkJsFn callback)

httpPost_raw : String -> String -> (String -> JS_IO ()) -> JS_IO ()
httpPost_raw url body callback =
  jscall
    ("function(){var xmlhttp=new XMLHttpRequest();"++
    "xmlhttp.onreadystatechange=function(){if(xmlhttp.readyState==4){"++
    "if(xmlhttp.status==200){%2(xmlhttp.responseText)}} };"++
    "xmlhttp.open('POST',%0, true);"++
    "xmlhttp.send(%1);}()")
    (String -> String -> (JsFn (String -> JS_IO ())) -> JS_IO ())
    url
    body
    (MkJsFn callback)
