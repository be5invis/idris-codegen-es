module Js.BrowserBase

import Js.ASync
import public Data.Vect
import public Js.BrowserDom
import public Js.Typeable

import Debug.Trace

data Path = PathHere | PathRight Path | PathLeft Path

Show Path where
  show PathHere = "PathHere"
  show (PathRight x) = "PathRight" ++ "(" ++ show x ++ ")"
  show (PathLeft x) = "PathLeft" ++ "(" ++ show x ++ ")"

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
  EmptyNode : View a
  TextNode : String -> View a
  InputNode : Maybe String -> View String
  AppendNode : View a -> View a -> View a
  MapNode : (a -> Maybe b) -> View a -> View b
  AjaxFormNode : View a -> View (FormEvent a)
  ContainerNode : String -> List (String, Maybe a) -> List (String, String) -> View a -> View a
  FoldNode : Typeable b => b -> View a -> (b -> View a) -> (a->b->(b, Maybe c)) -> Maybe (b->b) -> View c
  SelectNode : Maybe (Fin n) -> Vect n String -> View (Fin n)
  UniqIdNode : (Int->View a) -> Maybe (Int, View a) -> View a

vLength : View a -> Nat
vLength EmptyNode = 0
vLength (TextNode _) = 1
vLength (InputNode _) = 1
vLength (AppendNode v1 v2) = vLength v1 + vLength v2
vLength (MapNode _ v) = vLength v
vLength (AjaxFormNode _) = 1
vLength (ContainerNode _ _ _ _) = 1
vLength (FoldNode _ v _ _ _) = vLength v
vLength (SelectNode _ _) = 1
vLength (UniqIdNode _ (Just (_, v))) = vLength v

public export
data App : (a:Type) -> (a->Type) -> Type -> Type where
  MkApp : {a:Type} ->
          {f: a->Type} ->
          {b: Type} ->
          a ->
          ((x:a) -> View (f x)) ->
          ((x:a) -> f x -> (a, ASync b)) ->
          (a -> b -> (a, ASync b)) ->
          App a f b

public export
InputType : App a b c -> Type
InputType {b} (MkApp x _ _ _) = b x

export
stepAppASync : (App a f b) -> b -> (App a f b, ASync b)
stepAppASync (MkApp x1 x2 x3 x4) y =
  let (ns, async) = x4 x1 y
  in (MkApp ns x2 x3 x4, async)

export
stepAppInput : (p: App a f b) -> InputType p -> (App a f b, ASync b)
stepAppInput (MkApp x1 x2 x3 x4) y =
  let (ns, async) = x3 x1 y
  in (MkApp ns x2 x3 x4, async)

export
renderApp : (p: App a f b) -> View (InputType p)
renderApp (MkApp s r _ _) = r s

--public export
data AppState : (b:Type) -> (b->Type) -> Type -> Type where
  MkAppState : (p: App b f a) ->
               (View (InputType p)) ->
               DomNode ->
               AppState b f a

data Ctx : (b:Type) -> (b->Type) -> Type -> Type where
  MkCtx : Ptr -> Ctx a b c

setAppState : Ctx a b c -> AppState a b c -> JS_IO ()
setAppState (MkCtx ctx) z = jscall "%0.app = %1" (Ptr -> Ptr -> JS_IO ()) ctx (believe_me z)

getAppState : Ctx a b c -> JS_IO (AppState a b c)
getAppState (MkCtx ctx) = believe_me <$> jscall "%0.app" ( Ptr -> JS_IO Ptr) ctx


setAttrs : DomNode -> List (String, String) -> JS_IO ()
setAttrs n (x::xs) =
  do
    setAttribute n x
    setAttrs n xs
setAttrs _ [] = pure ()

removeAttrs : DomNode -> List String -> JS_IO ()
removeAttrs n (x::xs) =
  do
    removeAttribute n x
    removeAttrs n xs
removeAttrs _ [] = pure ()

record ViewContext where
  constructor MkViewContext
  container : DomNode
  position : Nat
  eventPath : (ViewEvent -> ViewEvent)
  procEvent : (ViewEvent -> JS_IO ())

addEvents : ViewContext -> DomNode -> List String -> JS_IO ()
addEvents vctx n (x::xs) =
  do
    registEvent (procEvent vctx) n x (eventPath vctx <$> (hereEvent $ pure x))
    addEvents vctx n xs
addEvents _ _ [] = pure ()

leftPart : ViewContext -> ViewContext
leftPart vctx = record {eventPath = \x => (eventPath vctx) $ leftEvent x} vctx

rightPart : ViewContext -> ViewContext
rightPart vctx = record {eventPath = \x => (eventPath vctx) $ rightEvent x} vctx

forward : Nat -> ViewContext -> ViewContext
forward n vctx = record {position = position vctx + n} vctx

vctxNode : Nat -> ViewContext -> JS_IO DomNode
vctxNode n vctx =
  do
    Just n <- child (n + position vctx) (container vctx)
    pure n

enterNode : DomNode -> ViewContext -> ViewContext
enterNode n vctx =
    record {container = n, position = 0} vctx

goVctxNode : Nat -> ViewContext -> JS_IO ViewContext
goVctxNode n vctx =
  do
    node <- vctxNode n vctx
    pure $ enterNode node vctx

removeView : ViewContext -> View a -> JS_IO ()
removeView vctx v =
  removeRange (container vctx) (position vctx) (vLength v)
  where
    removeRange c pos Z = pure ()
    removeRange c pos (S n) = removeChild pos c >>= \_ => removeRange c pos n


mutual
  updateFoldNodeState : (Typeable s, Typeable t) => Maybe (t->t) -> s -> t -> t
  updateFoldNodeState {t} u w1 w2 =
    case the (Maybe t) (tcast w1) of
      Nothing => w2
      Just w1' => case u of
                    Nothing => w1'
                    Just u' => u' w1'


  updateNodeView : ViewContext -> View a -> View b -> JS_IO (View b)
  updateNodeView vctx EmptyNode EmptyNode = pure EmptyNode
  updateNodeView vctx (TextNode sOld) (TextNode sNew) =
    if sOld == sNew then pure $ TextNode sNew
      else
        do
          setText sNew !(vctxNode 0 vctx)
          pure $ TextNode sNew
  updateNodeView vctx (InputNode _) (InputNode force) =
    case force of
      Nothing => pure $ InputNode Nothing
      Just s =>
        do
          setValue s !(vctxNode 0 vctx)
          pure $ InputNode Nothing
  updateNodeView vctx (AppendNode x y) (AppendNode z w) =
    do
      v1 <- updateNodeView (leftPart vctx) x z
      v2 <- updateNodeView (forward (vLength v1) $ rightPart vctx) y w
      pure $ AppendNode v1 v2
  updateNodeView vctx (MapNode _ v1) (MapNode f2 v2) =
    pure $ MapNode f2 !(updateNodeView vctx v1 v2)
  updateNodeView vctx (AjaxFormNode v1) (AjaxFormNode v2) =
    do
      v3 <- updateNodeView !(goVctxNode 0 $ leftPart vctx) v1 v2
      pure $ AjaxFormNode v3
  updateNodeView vctx vi@(ContainerNode t1 e1 a1 v1) vf@(ContainerNode t2 e2 a2 v2) =
    if t1 == t2 then
      do
        c <- vctxNode 0 vctx
        v3 <- updateNodeView (enterNode c $ leftPart vctx) v1 v2
        addEvents vctx c $ (map fst e2) \\ (map fst e1)
        setAttrs c $ a2 \\ a1
        removeAttrs c $ (map fst a1) \\ (map fst a2)
        let old = map (\x => (x, Nothing)) $ (map fst e1) \\ (map fst e2)
        pure $ ContainerNode t2 (e2 ++ old) a2 v3
      else do
        removeView vctx vi
        initViewDom vctx vf
  updateNodeView vctx (FoldNode s1 v1 _ _ _) (FoldNode s2 _ vf f u) =
    do
      let s3 = updateFoldNodeState u s1 s2
      v2 <- updateNodeView vctx v1 (vf s3)
      pure $ FoldNode s3 v2 vf f Nothing
  updateNodeView vctx vi@(SelectNode _ o1) vf@(SelectNode force o2) =
    if toList o1 == toList o2 then
      case force of
        Nothing => pure vf
        Just x =>
          do
            setValue (cast $ finToInteger x) !(vctxNode 0 vctx)
            pure vf
      else
        do
          removeView vctx vi
          initViewDom vctx vf
  updateNodeView vctx (UniqIdNode _ (Just (id,vOld))) (UniqIdNode r _) =
    do
      vNew <- updateNodeView vctx vOld (r id)
      pure $ UniqIdNode r (Just (id, vNew))
  updateNodeView vctx vi vf =
    do
      removeView vctx vi
      initViewDom vctx vf


  addOption : DomNode -> (Fin n, String) -> JS_IO ()
  addOption n (v, l) =
    do
      o <- appendNode "option" n
      setValue (cast $ finToInteger v) o
      setText l o

  initViewDom : ViewContext -> View c -> JS_IO (View c)
  initViewDom vctx EmptyNode = pure EmptyNode
  initViewDom vctx (TextNode s) =
    do
      span <- insertNodePos "span" (container vctx) (position vctx)
      setText s span
      pure $ TextNode s
  initViewDom vctx (InputNode force) =
    do
      i <- insertNodePos "input" (container vctx) (position vctx)
      registEvent (procEvent vctx) i "change" ( eventPath vctx <$> hereEvent targetValue)
      case force of
        Nothing => pure ()
        Just s => setValue s i
      pure $ InputNode force
  initViewDom vctx (AppendNode x y) =
    do
      v1 <- initViewDom (leftPart vctx) x
      v2 <-initViewDom (forward (vLength x) $ rightPart vctx) y
      pure $ AppendNode v1 v2
  initViewDom vctx (MapNode f v) = MapNode f <$> initViewDom vctx v
  initViewDom vctx (AjaxFormNode v) =
    do
      f <- insertNodePos "form" (container vctx) (position vctx)
      registEvent (procEvent vctx) f "submit" (eventPath vctx <$> (hereEvent $ preventDefault >>= \_=> pure ""))
      v1 <- initViewDom (enterNode f $ leftPart vctx) v
      pure $ AjaxFormNode v1
  initViewDom vctx (ContainerNode tag events attributes v) =
    do
      c <- insertNodePos tag (container vctx) (position vctx)
      addEvents vctx c (map fst events)
      setAttrs c attributes
      v1 <- initViewDom (enterNode c $ leftPart vctx) v
      pure $ ContainerNode tag events attributes v1
  initViewDom vctx (FoldNode a1 v a2 a3 a4) =
    do
      v1 <- initViewDom vctx v
      pure $ FoldNode a1 v1 a2 a3 a4
  initViewDom vctx (SelectNode force options) =
    do
      s <- insertNodePos "select" (container vctx) (position vctx)
      let options' = Data.Vect.zip range options
      sequence $ map (\x=> addOption s x) options'
      registEvent (procEvent vctx) s "change" (eventPath vctx <$> hereEvent targetValue)
      case force of
        Nothing => pure ()
        Just x => setValue (cast $ finToInteger x) s
      pure $ SelectNode force options
  initViewDom vctx (UniqIdNode r Nothing) =
    do
      id <- genId
      v <- initViewDom vctx (r id)
      pure (UniqIdNode r (Just (id, v)) )



  updateNodeEvent : ViewContext -> ViewEvent -> View a -> JS_IO (View a, Maybe a)
  updateNodeEvent vctx (PathHere, e) (InputNode f) =
    pure (InputNode Nothing, Just e)
  updateNodeEvent vctx (PathLeft x, e) (AppendNode y z) =
    do
      (ny, v) <- updateNodeEvent (leftPart vctx) (x,e) y
      pure (AppendNode ny z, v)
  updateNodeEvent vctx (PathRight x, e) (AppendNode y z) =
    do
      (nz, v) <- updateNodeEvent (forward (vLength y) $ rightPart vctx) (x,e) z
      pure (AppendNode y nz, v)
  updateNodeEvent vctx e (MapNode f v) =
    do
      (v2, x) <- updateNodeEvent vctx e v
      pure (MapNode f v2, x >>= f)
  updateNodeEvent vctx (PathHere, _) (AjaxFormNode v) =
    pure (AjaxFormNode v, Just Submit)
  updateNodeEvent vctx (PathLeft p, e) (AjaxFormNode v) =
    do
      (v2, x) <- updateNodeEvent !(goVctxNode 0 $ leftPart vctx) (p,e) v
      pure (AjaxFormNode v2, Value <$> x)
  updateNodeEvent vctx (PathHere, e)  c@(ContainerNode _ evts _ _) =
      pure (c, join $ lookup e evts)
  updateNodeEvent vctx (PathLeft p, e) (ContainerNode t evts attrs v) =
    do
      (v2, x) <- updateNodeEvent !(goVctxNode 0 $ leftPart vctx) (p, e) v
      pure (ContainerNode t evts attrs v2, x)
  updateNodeEvent vctx e (FoldNode s v vf f _) =
    do
      (v2, x) <- updateNodeEvent vctx e v
      case x of
        Nothing =>
          pure (FoldNode s v vf f Nothing, Nothing)
        Just y =>
          do
            let (s2, z) = f y s
            v3 <- updateNodeView vctx v2 (vf s2)
            pure (FoldNode s2 v3 vf f Nothing, z)
  updateNodeEvent vctx (PathHere, e) (SelectNode _ options) =
    let i = the Integer $ cast e
    in pure (SelectNode Nothing options, integerToFin i _)
  updateNodeEvent vctx e (UniqIdNode r (Just (id, v)) ) =
    do
      (v2, x) <- updateNodeEvent vctx e v
      pure (UniqIdNode r $ Just (id, v2), x)
  updateNodeEvent vctx (p, e) v =
    do
      putStr' $ "Internal error processing event " ++ e ++ " on path " ++ show p
      pure (v, Nothing)


  updateAppVal : Ctx a b c -> c -> JS_IO ()
  updateAppVal ctx z =
    do
      (MkAppState app lastV cont) <- getAppState ctx
      let (newApp, async) = stepAppASync app z
      let vNew = renderApp newApp
      finalView <- updateNodeView (MkViewContext cont 0 id (updateApp ctx)) lastV vNew
      setAppState ctx (MkAppState newApp finalView cont)
      setASync (updateAppVal ctx) async

  updateApp : Ctx a b c -> ViewEvent -> JS_IO ()
  updateApp ctx e =
    do
      (MkAppState app lastV cont) <- getAppState ctx
      (n2, mVal) <- updateNodeEvent (MkViewContext cont 0 id (updateApp ctx)) e lastV
      case mVal of
        Nothing => setAppState ctx (MkAppState app n2 cont)
        Just z =>
          do
            let (newApp, async) = stepAppInput app z
            let vNew = renderApp newApp
            finalView <- updateNodeView (MkViewContext cont 0 id (updateApp ctx)) n2 vNew
            setAppState ctx (MkAppState newApp finalView cont)
            setASync (updateAppVal ctx) async


  initView : Ctx a b c -> DomNode -> View d -> JS_IO (View d)
  initView ctx c view =
    initViewDom (MkViewContext c 0 id (updateApp ctx)) view

export
runApp : App a f b -> JS_IO ()
runApp {a} {f} {b} app =
  do
    c <- body
    ctxPtr <- jscall "{}" (() -> JS_IO Ptr) ()
    let ctx = the (Ctx a f b) $ MkCtx ctxPtr
    let v = renderApp app
    v1 <- initView ctx c v
    let appSt = MkAppState app v1 c
    setAppState ctx $ appSt

-------- View Instances ----
export
Functor View where
  map f x = MapNode (\x => Just $ f x) x

export
Semigroup (View t) where
  (<+>) a b = AppendNode a b

export
Monoid (View t) where
  neutral = EmptyNode

-------- Primitives --------

export
mapFilter : (a -> Maybe b) -> View a -> View b
mapFilter f x = MapNode f x

infixr 7 ++
export
(++) : View a -> View a -> View a
(++) x y = AppendNode x y

export
foldv : Typeable b => b -> (b->View a) -> (a->b->(b, Maybe c)) -> Maybe (b->b) -> View c
foldv x y f z =
  case z of
    Just w => FoldNode (w x) (y $ w x) y f z
    Nothing => FoldNode x (y x) y f z

export
containerNode : String -> List (String, Maybe a) -> List (String, String) -> View a -> View a
containerNode = ContainerNode

export
textNode : String -> View a
textNode = TextNode

export
inputNode : Maybe String -> View String
inputNode = InputNode

export
selectNode : Maybe (Fin n) -> Vect n String -> View (Fin n)
selectNode = SelectNode

export
ajaxFormNode : View a -> View (FormEvent a)
ajaxFormNode = AjaxFormNode

export
uniqIdView : (Int->View a) -> View a
uniqIdView x = UniqIdNode x Nothing

export
empty : View a
empty = EmptyNode
