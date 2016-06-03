module Js.BrowserBase

import Js.ASync
import public Data.Vect
import public Js.BrowserDom
import public Js.Typeable

import Debug.Trace

data Path = PathHere | PathRight Path | PathLeft Path

ViewEvent : Type
ViewEvent = (Path, String)

hereEvent : DomEvent String -> DomEvent ViewEvent
hereEvent x = (\y => (PathHere, y)) <$> x

leftEvent : ViewEvent -> ViewEvent
leftEvent (p, s) = (PathLeft p,s)

rightEvent : ViewEvent -> ViewEvent
rightEvent (p, s) = (PathRight p, s)

public export
data FormEvent a = Value a | Submit

export
data View : Type -> Type where
  TextNode : String -> View a
  InputNode : Maybe String -> View String
  AppendNode : View a -> View a -> View a
  MapNode : (a -> Maybe b) -> View a -> View b
  AjaxFormNode : View a -> View (FormEvent a)
  SimpleContainer : String -> View a -> View a
  FoldNode : Typeable b => b -> View a -> (b -> View a) -> (a->b->(b, Maybe c)) -> Maybe (b->b) -> View c

public export
record App a b where
  constructor MkApp
  state : b
  render : b -> View a
  update : a -> b -> (b, ASync a)

record AppState a b where
  constructor MkAppState
  theApp : App a b
  lastView : View a
  container : DomNode

data Ctx a b = MkCtx Ptr

setAppState : Ctx a b -> AppState a b -> JS_IO ()
setAppState (MkCtx ctx) z = jscall "%0.app = %1" (Ptr -> Ptr -> JS_IO ()) ctx (believe_me z)

getAppState : Ctx a b -> JS_IO (AppState a b)
getAppState (MkCtx ctx) = believe_me <$> jscall "%0.app" ( Ptr -> JS_IO Ptr) ctx


mutual

  updateFoldNodeState : (Typeable s, Typeable t) => Maybe (t->t) -> s -> t -> t
  updateFoldNodeState {t} u w1 w2 =
    case the (Maybe t) (tcast w1) of
      Nothing => w2
      Just w1' => case u of
                    Nothing => w1'
                    Just u' => u' w1'

  updateNodeView : View a -> View b -> Dom ViewEvent (View b)
  updateNodeView (TextNode sOld) (TextNode sNew) =
    if sOld == sNew then pure $ TextNode sNew
      else
        do
          setText sNew root
          pure $ TextNode sNew
  updateNodeView (InputNode _) (InputNode force) =
    case force of
      Nothing => pure $ InputNode force
      Just s =>
        do
          setValue s (child 0 root)
          pure $ InputNode force
  updateNodeView (AppendNode x y) (AppendNode z w) =
    do
      Just v1 <- chrootDom (child 0 root) (applyEvents leftEvent $ updateNodeView x z)
      Just v2 <- chrootDom (child 1 root) (applyEvents rightEvent $ updateNodeView y w)
      pure $ AppendNode v1 v2
  updateNodeView (MapNode _ v1) (MapNode f2 v2) =
    pure $ MapNode f2 !(updateNodeView v1 v2)
  updateNodeView (AjaxFormNode v1) (AjaxFormNode v2) =
    do
      Just v3 <- chrootDom (child 0 root) (applyEvents leftEvent $ updateNodeView v1 v2)
      pure $ AjaxFormNode v3
  updateNodeView (SimpleContainer t1 v1) vf@(SimpleContainer t2 v2) =
    if t1 == t2 then
      do
        Just v3 <- chrootDom (child 0 root) $ updateNodeView v1 v2
        pure $ SimpleContainer t2 v3
      else do
        clear root
        initViewDom vf
        pure vf
  updateNodeView (FoldNode s1 v1 _ _ _) (FoldNode s2 _ vf f u) =
    do
      let s3 = updateFoldNodeState u s1 s2
      v2 <- updateNodeView v1 (vf s3)
      pure $ FoldNode s3 v2 vf f Nothing
  updateNodeView _ v =
    do
      clear root
      initViewDom v
      pure v

  initViewDom : View c -> Dom ViewEvent ()
  initViewDom (TextNode s) =
    setText s root
  initViewDom (InputNode force) =
    do
      Just i <- appendNode "input" root
      registEvent i "change" (hereEvent targetValue)
      case force of
        Nothing => pure ()
        Just s => setValue s i
  initViewDom (AppendNode x y) =
    do
      Just c1 <- appendNode "span" root
      Just c2 <- appendNode "span" root
      chrootDom c1 (applyEvents leftEvent $ initViewDom x)
      chrootDom c2 (applyEvents rightEvent $ initViewDom y)
      pure ()
  initViewDom (MapNode _ v) = initViewDom v
  initViewDom (AjaxFormNode v) =
    do
      Just f <- appendNode "form" root
      registEvent f "submit" (hereEvent $ preventDefault >>= \_=> pure "")
      chrootDom f (applyEvents leftEvent $ initViewDom v)
      pure ()
  initViewDom (SimpleContainer tag v) =
    do
      Just c <- appendNode tag root
      chrootDom c (initViewDom v)
      pure ()
  initViewDom (FoldNode _ v _ _ _ ) = initViewDom v

  updateNodeEvent : ViewEvent -> View a -> Dom ViewEvent (View a, Maybe a)
  updateNodeEvent (PathHere, e) (InputNode f) =
    pure (InputNode Nothing, Just e)
  updateNodeEvent (PathLeft x, e) (AppendNode y z) =
    do
      Just (ny, v) <- chrootDom (child 0 root) (applyEvents leftEvent $ updateNodeEvent (x, e) y)
      pure (AppendNode ny z, v)
  updateNodeEvent (PathRight x, e) (AppendNode y z) =
    do
      Just (nz, v) <- chrootDom (child 1 root) (applyEvents rightEvent $ updateNodeEvent (x, e) z)
      pure (AppendNode y nz, v)
  updateNodeEvent e (MapNode f v) =
    do
      (v2, x) <- updateNodeEvent e v
      pure (MapNode f v2, x >>= f)
  updateNodeEvent (PathHere, _) (AjaxFormNode v) =
    pure (AjaxFormNode v, Just Submit)
  updateNodeEvent (PathLeft p, e) (AjaxFormNode v) =
    do
      Just (v2, x) <- chrootDom (child 0 root) (applyEvents leftEvent $ updateNodeEvent (p,e) v)
      pure (AjaxFormNode v2, Value <$> x)
  updateNodeEvent e (SimpleContainer t v) =
    do
      Just (v2, x) <- chrootDom (child 0 root) $ updateNodeEvent e v
      pure (SimpleContainer t v2, x)
  updateNodeEvent e (FoldNode s v vf f _) =
    do
      (v2, x) <- updateNodeEvent e v
      case x of
        Nothing =>
          pure (FoldNode s v vf f Nothing, Nothing)
        Just y =>
          do
            let (s2, z) = f y s
            v3 <- updateNodeView v (vf s2)
            pure (FoldNode s2 v3 vf f Nothing, z)

  updateAppVal : Ctx a b -> a -> JS_IO ()
  updateAppVal ctx x =
    do
      appSt <- getAppState ctx
      let app = theApp appSt
      let (newS, async) = (update app) x (state app)
      let vOld = lastView appSt
      let vNew = (render app) newS
      newViewNode <- runDom (container appSt) (updateApp ctx) (updateNodeView vOld vNew)
      setAppState ctx (record{lastView = newViewNode, theApp = record{state = newS} app} appSt)
      setASync (updateAppVal ctx) async

  updateApp : Ctx a b -> ViewEvent -> JS_IO ()
  updateApp ctx e =
    do
      appSt <- getAppState ctx
      (n2, mVal) <- runDom (container appSt) (updateApp ctx) (updateNodeEvent e (lastView appSt))
      setAppState ctx (record{lastView = n2} appSt)
      case mVal of
        Nothing => pure ()
        Just x => updateAppVal ctx x

  initView : Ctx a b -> DomNode -> View d -> JS_IO ()
  initView ctx container view =
      runDom container (updateApp ctx) (initViewDom view)

startApp : Ctx a b -> App a b -> DomNode -> JS_IO ()
startApp ctx x container =
  do
    let v = render x $ state x
    c <- appendNode' "span" container
    initView ctx c v
    setAppState ctx $ MkAppState x v c


export
runApp : App a b -> JS_IO ()
runApp {a} {b} app =
  do
    bo <- body
    c <- appendNode' "span" bo
    ctx <- jscall "{}" (() -> JS_IO Ptr) ()
    startApp (the (Ctx a b) $ MkCtx ctx) app c

-------- View Instances ----
export
Functor View where
  map f x = MapNode (\x => Just $ f x) x

export
Semigroup (View t) where
  (<+>) a b = AppendNode a b

export
Monoid (View t) where
  neutral = TextNode ""

-------- Primitives --------

export
text : String -> View a
text s = TextNode s

export
textinput : Maybe String -> View String
textinput x = InputNode x

export
textinput' : View String
textinput' = textinput Nothing

infixr  7 ++
export
(++) : View a -> View a -> View a
(++) x y = AppendNode x y


export
ajaxForm : View a -> View (FormEvent a)
ajaxForm x = AjaxFormNode x

export
foldp : Typeable b => b -> (b->View a) -> (a->b->(b, Maybe c)) -> Maybe (b->b) -> View c
foldp x y f z =
  case z of
    Just w => FoldNode (w x) (y $ w x) y f z
    Nothing => FoldNode x (y x) y f z

export
div : View a -> View a
div x = SimpleContainer "div" x
