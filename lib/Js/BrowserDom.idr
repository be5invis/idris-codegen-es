module Js.BrowserDom

import Js.BrowserForeigns

export
data DomNode  = MkDomNode Ptr

export
data DomPath = MkDomPath (DomNode -> JS_IO (Maybe DomNode) )

export
data DomEvent a = MkDomEvent (Ptr -> JS_IO a)

export
data Dom e a = MkDom (DomNode -> (e -> JS_IO ()) -> JS_IO a)

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
lengthChilds' : DomNode -> JS_IO Int
lengthChilds' (MkDomNode p) = lenChilds p

export
solvePath : DomPath -> DomNode -> JS_IO(Maybe DomNode)
solvePath (MkDomPath f) x = f x

export
clear' : DomNode -> JS_IO ()
clear' (MkDomNode x) = clearContents x

export
runDom : DomNode -> (e -> JS_IO ()) -> Dom e a -> JS_IO a
runDom container procE (MkDom x) =
  x container procE

export
chrootDom : DomPath -> Dom e a -> Dom e (Maybe a)
chrootDom path ori = MkDom $ \x, y =>
  case !(solvePath path x) of
    Nothing => pure Nothing
    Just z => Just <$> runDom z y ori

export
applyEvents : (e->i) -> Dom e a -> Dom i a
applyEvents f ori = MkDom $ \x, y =>  runDom x (y . f) ori

export
root : DomPath
root = MkDomPath (\x => pure $ Just x)

export
child : Nat -> DomPath -> DomPath
child pos path = MkDomPath $ \x =>
  do
    base <- solvePath path x
    case base of
      Nothing => pure Nothing
      Just x => child' pos x

export
body : JS_IO DomNode
body = MkDomNode <$> docBody

export
domLog : String -> Dom e ()
domLog s = MkDom $ \_, _=> putStr' s

export
domLogPath : DomPath -> Dom e ()
domLogPath p = MkDom $ \x, _=>
    case !(solvePath p x) of
      Nothing => putStr' "undefined"
      Just (MkDomNode y) => jscall "console.log(%0)" (Ptr -> JS_IO ()) y

export
appendNode : String -> DomPath -> Dom e (Maybe DomPath)
appendNode tag path = MkDom $ \node, _ =>
    case !(solvePath path node) of
      Nothing => pure Nothing
      Just (MkDomNode n) =>
        do
          p <- appendChild n !(createElement tag)
          pure $ Just $ MkDomPath (\_ => pure $ Just $ MkDomNode p)

export
clear : DomPath -> Dom e ()
clear path = MkDom $ \node, _ =>
    case !(solvePath path node) of
      Nothing => putStr' "Warning: unsolvable path"
      Just x => clear' x


export
setValue : String -> DomPath -> Dom e ()
setValue s path = MkDom $ \node, _ =>
  case !(solvePath path node) of
    Nothing => putStr' "Warning: unsolvable path"
    Just (MkDomNode p) => setVal p s

export
setText : String -> DomPath -> Dom e ()
setText s (MkDomPath path) = MkDom $ \node, _ =>
    case !(path node) of
      Just (MkDomNode n) => setTextContent n s

export
registEvent : DomPath -> String -> DomEvent e -> Dom e ()
registEvent (MkDomPath path) eventType (MkDomEvent getDomE) = MkDom $ \node, proc =>
  case !(path node) of
    Nothing => pure ()
    Just (MkDomNode n) => addEventListener n eventType (\x => getDomE x >>= proc  )

export
targetValue : DomEvent String
targetValue = MkDomEvent $ \x => jscall "%0.target.value" (Ptr -> JS_IO String) x

export
preventDefault : DomEvent ()
preventDefault = MkDomEvent $ \x => jscall "%0.preventDefault()" (Ptr -> JS_IO ()) x
