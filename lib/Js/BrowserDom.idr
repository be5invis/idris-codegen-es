module Js.BrowserDom

import Js.BrowserForeigns

export
data DomNode  = MkDomNode Ptr

export
data DomEvent a = MkDomEvent (Ptr -> JS_IO a)

export
Functor DomEvent where
  map f (MkDomEvent de) = MkDomEvent $ \x => f <$> de x

export
Applicative DomEvent where
  pure a = MkDomEvent $ \x => pure a

  (<*>) (MkDomEvent f) (MkDomEvent fa) =
    MkDomEvent $ \x => f x <*> fa x

export
Monad DomEvent where
  (>>=) (MkDomEvent fa) f =
    MkDomEvent $ \x =>
      do
        a <- fa x
        let MkDomEvent g = f a
        g x


export
appendNode : String -> DomNode -> JS_IO DomNode
appendNode tag (MkDomNode n) = MkDomNode <$> appendChild n !(createElement tag)


export
child : Nat -> DomNode -> JS_IO (Maybe DomNode)
child i (MkDomNode p) =
  if !(lenChilds p) > (cast i) then (Just . MkDomNode) <$> childNode (cast i) p
    else pure Nothing

export
lengthChilds : DomNode -> JS_IO Int
lengthChilds (MkDomNode p) = lenChilds p


export
clear : DomNode -> JS_IO ()
clear (MkDomNode x) = clearContents x

export
removeChild : Nat -> DomNode -> JS_IO ()
removeChild n (MkDomNode node) = removeChildNode node (cast n)


export
body : JS_IO DomNode
body = MkDomNode <$> docBody

export
registEvent : (e -> JS_IO ()) -> DomNode -> String -> DomEvent e -> JS_IO ()
registEvent proc (MkDomNode n) eventType (MkDomEvent getDomE) =
    addEventListener n eventType (\x => getDomE x >>= proc  )

export
logNode : DomNode -> JS_IO ()
logNode (MkDomNode node) =
  jscall "console.log(%0)" (Ptr -> JS_IO ()) node

export
setValue : String -> DomNode -> JS_IO ()
setValue s (MkDomNode node) =
  setVal node s

export
setText : String -> DomNode -> JS_IO ()
setText s (MkDomNode node) =
  do
    setTextContent node s

export
insertNodePos : String -> DomNode -> Nat -> JS_IO DomNode
insertNodePos tag node@(MkDomNode y) pos =
  do
    c <- child pos node
    case c of
      Nothing => appendNode tag node
      Just (MkDomNode z) => MkDomNode <$> insertBefore y !(createElement tag) z

export
setAttribute : DomNode -> (String, String) -> JS_IO ()
setAttribute (MkDomNode n) attr =
    setAttr n attr

export
removeAttribute : DomNode -> String -> JS_IO ()
removeAttribute (MkDomNode node) name = removeAttr node name

export
targetValue : DomEvent String
targetValue = MkDomEvent $ \x => jscall "%0.target.value" (Ptr -> JS_IO String) x

export
preventDefault : DomEvent ()
preventDefault = MkDomEvent $ \x => jscall "%0.preventDefault()" (Ptr -> JS_IO ()) x

export
genId : JS_IO Int
genId =
    jscall
        ("(function(){" ++
         "    if(window.idris_js_global_id_counter){" ++
         "      window.idris_js_global_id_counter += 1;" ++
         "    }else{" ++
         "      window.idris_js_global_id_counter = 0;" ++
         "    }" ++
         "    return window.idris_js_global_id_counter;" ++
         "})()"
        )
        (() -> JS_IO Int)
        ()
