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
ViewEvent = (Path, Ptr )

hereEvent : DomEvent Ptr -> DomEvent ViewEvent
hereEvent x = (\y => (PathHere, y)) <$> x

hereEventStr : DomEvent String -> DomEvent ViewEvent
hereEventStr x = (\y => (PathHere, believe_me y)) <$> x

leftEvent : ViewEvent -> ViewEvent
leftEvent (p, s) = (PathLeft p,s)

rightEvent : ViewEvent -> ViewEvent
rightEvent (p, s) = (PathRight p, s)

public export
data FormEvent a = Value a | Submit

data InputNodeType : Type -> Type where
  Text : String -> InputNodeType String
  FileSelector : InputNodeType (Maybe DomFile)
  Select : (Vect n String) -> InputNodeType (Fin n)

hereEventInput : InputNodeType a -> DomEvent (Maybe a) -> DomEvent ViewEvent
hereEventInput _ x = (\y => (PathHere, believe_me y)) <$> x

setValInput : a -> InputNodeType a -> DomNode -> JS_IO ()
setValInput x (Text _) node = setValue x node
setValInput x (Select opts) node = setValue (cast $ finToInteger x) node

addOption : DomNode -> (Fin n, String) -> JS_IO ()
addOption n (v, l) =
  do
    o <- appendNode "option" n
    setValue (cast $ finToInteger v) o
    setText l o

initInput : DomNode -> Nat -> InputNodeType a -> JS_IO DomNode
initInput container pos (Text placeholder) =
  do
    i <- insertNodePos "input" container pos
    setAttribute i ("type","text")
    setAttribute i ("placeholder", placeholder)
    pure i
initInput container pos (Select options) =
  do
    s <- insertNodePos "select" container pos
    let options' = Data.Vect.zip range options
    sequence $ map (\x=> addOption s x) options'
    pure s
initInput container pos FileSelector =
  do
    i <- insertNodePos "input" container pos
    setAttribute i ("type","file")
    pure i

updateInput : DomNode -> Nat -> InputNodeType a -> InputNodeType b -> JS_IO ()
updateInput container pos (Text p1) (Text p2) =
  if p1 == p2 then pure ()
    else
      do
        Just c <- child pos container
        setAttribute c ("placeholder", p2)
updateInput container pos FileSelector FileSelector = pure ()
updateInput container pos (Select o1) (Select o2) =
  if toList o1 == toList o2 then pure ()
    else
      do
        removeChild pos container
        initInput container pos (Select o2)
        pure ()

inputChangeEvent : InputNodeType a -> DomEvent (Maybe a)
inputChangeEvent (Text _) = Just <$> targetValue
inputChangeEvent (Select opts {n}) = (\x => integerToFin (the Integer $ cast x) n ) <$> targetValue
inputChangeEvent FileSelector = Just <$> targetFile

export
data View : Type -> Type where
  EmptyNode : View a
  TextNode : String -> List (String, Maybe a) -> List (String, String) -> String -> View a
  InputNode : Maybe a -> InputNodeType a -> View a
  AppendNode : View a -> View a -> View a
  MapNode : (a -> Maybe b) -> View a -> View b
  AjaxFormNode : View a -> View (FormEvent a)
  ContainerNode : String -> List (String, Maybe a) -> List (String, String) -> View a -> View a
  FoldNode : Typeable b => b -> View a -> (b -> View a) -> (b->a->(b, Maybe c)) -> Maybe (b->b) -> View c
  UniqIdNode : (Int->View a) -> Maybe (Int, View a) -> View a

vLength : View a -> Nat
vLength EmptyNode = 0
vLength (TextNode _ _ _ _) = 1
vLength (InputNode _ _) = 1
vLength (AppendNode v1 v2) = vLength v1 + vLength v2
vLength (MapNode _ v) = vLength v
vLength (AjaxFormNode _) = 1
vLength (ContainerNode _ _ _ _) = 1
vLength (FoldNode _ v _ _ _) = vLength v
vLength (UniqIdNode _ (Just (_, v))) = vLength v

export
data AppM b a = MkAppM ( (ASync b -> JS_IO ()) -> JS_IO a )

export
Functor (AppM b) where
  map f (MkAppM x) = MkAppM $ \proc => f <$> (x proc)

export
Applicative (AppM b) where
  pure a = MkAppM $ \proc => pure a

  (<*>) (MkAppM x) (MkAppM y) = MkAppM $ \proc => (x proc) <*> (y proc)

export
Monad (AppM b) where
  (>>=) (MkAppM x) f =
    MkAppM $
      \proc => do
        (MkAppM y) <- f <$> (x proc)
        y proc

export
createEvent : ASync b -> AppM b ()
createEvent x = MkAppM $ \proc => proc x

export
liftJS_IO : JS_IO a -> AppM b a
liftJS_IO x = MkAppM (\onevt => x)


runAppM : (ASync b -> JS_IO ()) -> AppM b a -> JS_IO a
runAppM x (MkAppM y) = y x

public export
data App : (a:Type) -> (a->Type) -> Type -> Type where
  MkApp : {a:Type} ->
          {f: a->Type} ->
          {b: Type} ->
          AppM b a ->
          ((x:a) -> View (f x)) ->
          ((x:a) -> f x -> AppM b a) ->
          (a -> b -> AppM b a) ->
          App a f b

data AppState : (a:Type) -> (a->Type) -> Type -> Type where
  MkAppState : (x: a) ->
               (View (f x)) ->
               DomNode ->
               AppState a f b
{-public export
InputType : App a b c -> Type
InputType {b} (MkApp x _ _ _) = b x
-}

export
stepAppASync : App a f b -> a -> b -> AppM b a
stepAppASync (MkApp x1 x2 x3 x4) x y = x4 x y

export
stepAppInput : App a f b -> (x: a) -> f x -> AppM b a
stepAppInput (MkApp x1 x2 x3 x4) x y = x3 x y

export
renderApp : App a f b -> (x: a) -> View (f x)
renderApp (MkApp _ r _ _) x = r x

export
getInit : App a f b -> AppM b a
getInit (MkApp x _ _ _) = x

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
    registEvent (procEvent vctx) n x (eventPath vctx <$> (hereEventStr $ pure x))
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
  updateNodeView vctx vi@(TextNode t1 e1 a1 txt1) vf@(TextNode t2 e2 a2 txt2) =
    if t1 == t2 then
      do
        c <- vctxNode 0 vctx
        if txt1 == txt2 then pure ()
          else
            setText txt2 c
        addEvents vctx c $ (map fst e2) \\ (map fst e1)
        setAttrs c $ a2 \\ a1
        removeAttrs c $ (map fst a1) \\ (map fst a2)
        let old = map (\x => (x, Nothing)) $ (map fst e1) \\ (map fst e2)
        pure $ TextNode t2 (e2 ++ old) a2 txt2
      else do
        removeView vctx vi
        initViewDom vctx vf
  updateNodeView vctx (InputNode _ t1 ) (InputNode force t2) =
    do
      c <- vctxNode 0 vctx
      updateInput (container vctx) (position vctx) t1 t2
      case force of
        Nothing =>
          pure $ InputNode Nothing t2
        Just s =>
          do
            setValInput s t2 c
            pure $ InputNode Nothing t2
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
  updateNodeView vctx (UniqIdNode _ (Just (id,vOld))) (UniqIdNode r _) =
    do
      vNew <- updateNodeView vctx vOld (r id)
      pure $ UniqIdNode r (Just (id, vNew))
  updateNodeView vctx vi vf =
    do
      removeView vctx vi
      initViewDom vctx vf



  initViewDom : ViewContext -> View c -> JS_IO (View c)
  initViewDom vctx EmptyNode = pure EmptyNode
  initViewDom vctx (TextNode tag events attributes txt) =
    do
      c <- insertNodePos tag (container vctx) (position vctx)
      addEvents vctx c (map fst events)
      setAttrs c attributes
      setText txt c
      pure $ TextNode tag events attributes txt
  initViewDom vctx (InputNode force t) =
    do
      i <- initInput (container vctx) (position vctx) t
      registEvent (procEvent vctx) i "change" (eventPath vctx <$> hereEventInput t (inputChangeEvent t))
      case force of
        Nothing => pure ()
        Just s => setValInput s t i
      pure $ InputNode Nothing t
  initViewDom vctx (AppendNode x y) =
    do
      v1 <- initViewDom (leftPart vctx) x
      v2 <-initViewDom (forward (vLength x) $ rightPart vctx) y
      pure $ AppendNode v1 v2
  initViewDom vctx (MapNode f v) = MapNode f <$> initViewDom vctx v
  initViewDom vctx (AjaxFormNode v) =
    do
      f <- insertNodePos "form" (container vctx) (position vctx)
      registEvent (procEvent vctx) f "submit" (eventPath vctx <$> (hereEventStr $ preventDefault >>= \_=> pure ""))
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
  initViewDom vctx (UniqIdNode r Nothing) =
    do
      id <- genId
      v <- initViewDom vctx (r id)
      pure (UniqIdNode r (Just (id, v)) )


  updateNodeEvent : ViewContext -> ViewEvent -> View a -> JS_IO (View a, Maybe a)
  updateNodeEvent vctx (PathHere, e)  c@(TextNode _ evts _ _) =
      pure (c, join $ lookup (believe_me e) evts)
  updateNodeEvent vctx (PathHere, e) (InputNode _ t) =
    pure (InputNode Nothing t, believe_me e)
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
      pure (c, join $ lookup (believe_me e) evts)
  updateNodeEvent vctx (PathLeft p, e) (ContainerNode t evts attrs v) =
    do
      (v2, x) <- updateNodeEvent !(goVctxNode 0 $ leftPart vctx) (p, e) v
      pure (ContainerNode t evts attrs v2, x)
  updateNodeEvent vctx e (FoldNode s v vf f _) =
    do
      (v2, x) <- updateNodeEvent vctx e v
      case x of
        Nothing =>
          pure (FoldNode s v2 vf f Nothing, Nothing)
        Just y =>
          do
            let (s2, z) = f s y
            v3 <- updateNodeView vctx v2 (vf s2)
            pure (FoldNode s2 v3 vf f Nothing, z)
  updateNodeEvent vctx e (UniqIdNode r (Just (id, v)) ) =
    do
      (v2, x) <- updateNodeEvent vctx e v
      pure (UniqIdNode r $ Just (id, v2), x)
  updateNodeEvent vctx (p, e) v =
    do
      putStr' $ "Internal error processing events on path" ++ show p
      pure (v, Nothing)

  runAndSetAppM : App a f b -> Ctx a f b -> AppM b a -> JS_IO a
  runAndSetAppM app ctx x = runAppM (setASync (updateAppVal app ctx) ) x


  updateAppVal : App a f b -> Ctx a f b -> b -> JS_IO ()
  updateAppVal app ctx z =
    do
      (MkAppState st lastV cont) <- getAppState ctx
      newSt <- runAndSetAppM app ctx $ stepAppASync app st z
      let vNew = renderApp app newSt
      finalView <- updateNodeView (MkViewContext cont 0 id (updateApp app ctx)) lastV vNew
      setAppState ctx (MkAppState newSt finalView cont)

  updateApp : App a f b -> Ctx a f b -> ViewEvent -> JS_IO ()
  updateApp app ctx e =
    do
      (MkAppState st lastV cont) <- getAppState ctx
      (n2, mVal) <- updateNodeEvent (MkViewContext cont 0 id (updateApp app ctx)) e lastV
      case mVal of
        Nothing => setAppState ctx (MkAppState st n2 cont)
        Just z =>
          do
            newSt <- runAndSetAppM app ctx $ stepAppInput app st z
            let vNew = renderApp app newSt
            finalView <- updateNodeView (MkViewContext cont 0 id (updateApp app ctx)) n2 vNew
            setAppState ctx (MkAppState newSt finalView cont)


  initView : App a f b -> Ctx a f b -> DomNode -> View d -> JS_IO (View d)
  initView app ctx c view =
    initViewDom (MkViewContext c 0 id (updateApp app ctx)) view


export
runApp : App a f b -> JS_IO ()
runApp {a} {f} {b} app =
  do
    c <- body
    ctxPtr <- jscall "{}" (() -> JS_IO Ptr) ()
    let ctx = the (Ctx a f b) $ MkCtx ctxPtr
    st <- runAndSetAppM app ctx $ getInit app
    let v = renderApp app st
    v1 <- initView app ctx c v
    let appSt = MkAppState st v1 c
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
foldv : Typeable b => b -> (b->View a) -> (b-> a ->(b, Maybe c)) -> Maybe (b->b) -> View c
foldv x y f z =
  case z of
    Just w => FoldNode (w x) (y $ w x) y f z
    Nothing => FoldNode x (y x) y f z

export
containerNode : String -> List (String, a) -> List (String, String) -> View a -> View a
containerNode x y z k = ContainerNode x (map (\(m,n)=>(m, Just n)) y) z k

export
textNode : String -> List (String, a) -> List (String, String) -> String -> View a
textNode x y z k = TextNode x (map (\(m,n)=>(m, Just n)) y) z k

export
textinputNode : String -> Maybe String -> View String
textinputNode placeholder x = InputNode x (Text placeholder)

export
selectNode : Maybe (Fin n) -> Vect n String -> View (Fin n)
selectNode x o = InputNode x (Select o)

export
ajaxFormNode : View a -> View (FormEvent a)
ajaxFormNode = AjaxFormNode

export
uniqIdView : (Int->View a) -> View a
uniqIdView x = UniqIdNode x Nothing

export
empty : View a
empty = EmptyNode

export
fileSelectorNode : View (Maybe DomFile)
fileSelectorNode = InputNode Nothing FileSelector
