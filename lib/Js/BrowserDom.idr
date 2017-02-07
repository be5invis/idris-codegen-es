module Js.BrowserDom

import Js.BrowserForeigns

public export
data DomNode  = MkDomNode Ptr

export
data DomEvent a = MkDomEvent (Ptr -> JS_IO a)

export
data DomFile = MkDomFile Ptr

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

public export
data FillType = Forwards | Backwards | Both | None | Auto

Show FillType where
  show Forwards = "forwards"
  show Backwards = "backwards"
  show Both = "both"
  show None = "none"
  show Auto = "auto"

public export
record AnimationConfig where
  constructor MkAnimationConfig
  duration : Nat
  fill : FillType

export
appendNodeNS : DomNode -> Maybe String -> String -> JS_IO DomNode
appendNodeNS (MkDomNode n) (Just ns) tag = MkDomNode <$> appendChild n !(createElementNS ns tag)
appendNodeNS (MkDomNode n) Nothing tag = MkDomNode <$> appendChild n !(createElement tag)

export
appendNode : DomNode -> String -> JS_IO DomNode
appendNode n tag = appendNodeNS n Nothing tag


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
removeChild n (MkDomNode node) = removeChildNode node !(childNode (cast n) node)

export
parent : DomNode -> JS_IO (Maybe DomNode)
parent (MkDomNode x) =
  do
    p <- parentNode x
    und <- isUndefined p
    if und then
      pure Nothing
      else pure $ Just $ MkDomNode p


export
removeDomNode : DomNode -> JS_IO ()
removeDomNode n@(MkDomNode n') =
  case !(parent n) of
    Nothing => pure ()
    Just (MkDomNode p) => removeChildNode p n'

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
      Nothing => appendNode node tag
      Just (MkDomNode z) => MkDomNode <$> insertBeforeNode y !(createElement tag) z

export
setAttribute : DomNode -> (String, String) -> JS_IO ()
setAttribute (MkDomNode n) attr =
    setAttr n attr

export
removeAttribute : DomNode -> String -> JS_IO ()
removeAttribute (MkDomNode node) name = removeAttr node name

export
setCSSProp : DomNode -> String -> String -> JS_IO ()
setCSSProp (MkDomNode node) name value = jscall "%0.style[%1]=%2" (Ptr -> String -> String -> JS_IO ()) node name value

export
animateCSS : AnimationConfig -> DomNode -> List (List (String, String)) -> JS_IO ()
animateCSS animConf (MkDomNode n) keyFrames =
  do
    opts <- makeJSObj $ [ ("duration", believe_me $ the (Int) $ cast $ duration animConf)
                        , ("fill", believe_me $ show $ fill animConf)
                        ]
    kFramesList <- sequence $ map makeJSStringObj keyFrames
    kFrames <- makeJSList kFramesList
    jscall "%0.animate(%1, %2)" (Ptr -> Ptr -> Ptr -> JS_IO ()) n kFrames opts

export
getDataAttr : DomNode -> String -> JS_IO String
getDataAttr (MkDomNode node) name =
  jscall "%0.dataset[%1] == undefined ? '' : %0.dataset[%1]" (Ptr -> String -> JS_IO String) node name

export
setDataAttr : DomNode -> String -> String -> JS_IO ()
setDataAttr (MkDomNode node) name val =
  jscall "%0.dataset[%1] = %2" (Ptr -> String -> String -> JS_IO ()) node name val

export
targetValue : DomEvent String
targetValue = MkDomEvent $ \x => jscall "%0.target.value" (Ptr -> JS_IO String) x

export
targetFile : DomEvent (Maybe DomFile)
targetFile =
  MkDomEvent $ \x =>
    do
      files <- jscall "%0.target.files[0]" (Ptr -> JS_IO Ptr) x
      length <- jscall "%0.length" (Ptr -> JS_IO Int) files
      if length == 0 then pure Nothing
        else Just <$> (MkDomFile <$> jscall "%0[0]" (Ptr -> JS_IO Ptr) files)

export
preventDefault : DomEvent ()
preventDefault = MkDomEvent $ \x => jscall "%0.preventDefault()" (Ptr -> JS_IO ()) x

export
genId : JS_IO Int
genId =
    jscall
        ("(function(){" ++
         "    if(window.idris_js_global_id_counter!=undefined){" ++
         "      window.idris_js_global_id_counter += 1;" ++
         "    }else{" ++
         "      window.idris_js_global_id_counter = 0;" ++
         "    }" ++
         "    return window.idris_js_global_id_counter;" ++
         "})()"
        )
        (() -> JS_IO Int)
        ()


export
onHashChange: ASync ()
onHashChange = MkASync (\x => jscall
                                "window.addEventListener('hashchange', %0, false)"
                                (( JsFn (() -> JS_IO ())) -> JS_IO ())
                                (MkJsFn x)
                       )

export
getHref : JS_IO String
getHref = jscall "window.location.href" (() -> JS_IO String) ()

export
getHash : JS_IO String
getHash = jscall "decodeURI(window.location.hash.substr(1))" (() -> JS_IO String) ()

export
getLocationSearch : JS_IO String
getLocationSearch = jscall "decodeURI(window.location.search)" (() -> JS_IO String) ()
