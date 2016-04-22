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
runDom : DomNode -> (e -> JS_IO ()) -> Dom e a -> JS_IO a
runDom (MkDomNode container) procE (MkDom x) =
  do
    e <- createElement "span"
    c <- appendChild container e
    x (MkDomNode c) procE


export
root : DomPath
root = MkDomPath (\x => Just x)

export
body : JS_IO DomNode
body = MkDomNode <$> docBody

export
consoleLog : String -> Dom e ()
consoleLog s = MkDom $ \_, _=> putStr' s

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
      Nothing => pure ()
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
