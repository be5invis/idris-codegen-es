module Js.BrowserDom

import Js.BrowserForeigns

export
data DomNode  = MkDomNode Ptr

export
data DomPath = MkDomPath (DomNode -> Maybe DomNode)

export
data DomEvent a = MkDomEvent (Ptr -> JS_IO a)

export
data Dom e a = MkDom (DomNode -> (e -> JS_IO ()) -> JS_IO a)


export
Functor (Dom e) where
  map f (MkDom fa) = MkDom $ \n, p => f <$> fa n p

export
Applicative (Dom e) where
  pure a = MkDom $ \_, _ => pure a

  (<*>) (MkDom f) (MkDom fa) = MkDom $ \n, p => f n p <*> fa n p

export
Monad (Dom e) where
  (>>=) (MkDom fa) f =
    MkDom $ \n, p =>
      do
        x <- fa n p
        let MkDom g = (f x)
        g n p

export
appendNode' : String -> DomNode -> JS_IO DomNode
appendNode' tag (MkDomNode n) = MkDomNode <$> appendChild n !(createElement tag)


export
child' : Nat -> DomNode -> JS_IO (Maybe DomNode)
child' i (MkDomNode p) =
  if !(lenChilds p) > (cast i) then (Just . MkDomNode) <$> childNode (cast i) p
    else pure Nothing

export
solvePath : DomPath -> DomNode -> Maybe DomNode
solvePath (MkDomPath f) x = f x

export
clear' : DomNode -> JS_IO ()
clear' (MkDomNode x) = clearContents x

export
runDom : DomNode -> (e -> JS_IO ()) -> Dom e a -> JS_IO a
runDom container procE (MkDom x) =
  x container procE


export
root : DomPath
root = MkDomPath (\x => Just x)

export
body : JS_IO DomNode
body = MkDomNode <$> docBody

export
domLog : String -> Dom e ()
domLog s = MkDom $ \_, _=> putStr' s

export
appendNode : String -> DomPath -> Dom e (Maybe DomPath)
appendNode tag (MkDomPath path) = MkDom $ \node, _ =>
    case path node of
      Nothing => pure Nothing
      Just (MkDomNode n) =>
        do
          p <- appendChild n !(createElement tag)
          pure $ Just $ MkDomPath (\_ => Just $ MkDomNode p)

export
setText : String -> DomPath -> Dom e ()
setText s (MkDomPath path) = MkDom $ \node, _ =>
    case path node of
      Just (MkDomNode n) => setTextContent n s

export
registEvent : DomPath -> String -> DomEvent e -> Dom e ()
registEvent (MkDomPath path) eventType (MkDomEvent getDomE) = MkDom $ \node, proc =>
  case path node of
    Nothing => pure ()
    Just (MkDomNode n) => addEventListener n eventType (\x => getDomE x >>= proc  )

export
targetValue : DomEvent String
targetValue = MkDomEvent $ \x => jscall "%0.target.value" (Ptr-> JS_IO String) x
