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
  ContainerNode : String -> List (String, Maybe a) -> List (String, String) -> View a -> View a
  FoldNode : Typeable b => b -> View a -> (b -> View a) -> (a->b->(b, Maybe c)) -> Maybe (b->b) -> View c
  SelectNode : Maybe (Fin n) -> Vect n String -> View (Fin n)
  UniqIdNode : (Int->View a) -> Maybe (Int, View a) -> View a


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

public export
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

addEvents : DomPath -> List String -> Dom ViewEvent ()
addEvents p (x::xs) =
  do
    registEvent p x (hereEvent $ pure x)
    addEvents p xs
addEvents p [] = pure ()

setAttrs : DomPath -> List (String, String) -> Dom e ()
setAttrs p (x::xs) =
  do
    setAttribute p x
    setAttrs p xs
setAttrs p [] = pure ()

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
      Nothing => pure $ InputNode Nothing
      Just s =>
        do
          setValue s (child 0 root)
          pure $ InputNode Nothing
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
  updateNodeView (ContainerNode t1 e1 a1 v1) vf@(ContainerNode t2 e2 a2 v2) =
    if t1 == t2 then
      do
        let c =  child 0 root
        Just v3 <- chrootDom c (applyEvents leftEvent $ updateNodeView v1 v2)
        addEvents c $ (map fst e2) \\ (map fst e1)
        setAttrs c $ a2 \\ a1
        let old = map (\x => (x, Nothing)) $ (map fst e1) \\ (map fst e2)
        pure $ ContainerNode t2 (e2 ++ old) a2 v3
      else do
        clear root
        initViewDom vf
        pure vf
  updateNodeView (FoldNode s1 v1 _ _ _) (FoldNode s2 _ vf f u) =
    do
      let s3 = updateFoldNodeState u s1 s2
      v2 <- updateNodeView v1 (vf s3)
      pure $ FoldNode s3 v2 vf f Nothing
  updateNodeView (SelectNode _ o1) vf@(SelectNode force o2) =
    if toList o1 == toList o2 then
      case force of
        Nothing => pure vf
        Just x =>
          do
            setValue (cast $ finToInteger x) (child 0 root)
            pure vf
      else
        do
          clear root
          initViewDom vf
          pure vf
  updateNodeView (UniqIdNode _ (Just (id,vOld))) (UniqIdNode r _) =
    do
      vNew <- updateNodeView vOld (r id)
      pure $ UniqIdNode r (Just (id, vNew))
  updateNodeView _ v =
    do
      clear root
      initViewDom v
      pure v

  addOption : DomPath -> (Fin n, String) -> Dom e ()
  addOption p (v, l) =
    do
      Just o <- appendNode "option" p
      setValue (cast $ finToInteger v) o
      setText l o

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
  initViewDom (ContainerNode tag events attributes v) =
    do
      Just c <- appendNode tag root
      addEvents c (map fst events)
      setAttrs c attributes
      chrootDom c (applyEvents leftEvent $ initViewDom v)
      pure ()
  initViewDom (FoldNode _ v _ _ _ ) = initViewDom v
  initViewDom (SelectNode force options) =
    do
      Just s <- appendNode "select" root
      let options' = Data.Vect.zip range options
      sequence $ map (\x=> addOption s x) options'
      registEvent s "change" (hereEvent targetValue)
      case force of
        Nothing => pure ()
        Just x => setValue (cast $ finToInteger x) s


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
  updateNodeEvent (PathHere, e)  c@(ContainerNode _ evts _ _) =
      pure (c, join $ lookup e evts)
  updateNodeEvent (PathLeft p, e) (ContainerNode t evts attrs v) =
    do
      Just (v2, x) <- chrootDom (child 0 root) (applyEvents leftEvent $ updateNodeEvent (p,e) v)
      pure (ContainerNode t evts attrs v2, x)
  updateNodeEvent e (FoldNode s v vf f _) =
    do
      (v2, x) <- updateNodeEvent e v
      case x of
        Nothing =>
          pure (FoldNode s v vf f Nothing, Nothing)
        Just y =>
          do
            let (s2, z) = f y s
            v3 <- updateNodeView v2 (vf s2)
            pure (FoldNode s2 v3 vf f Nothing, z)
  updateNodeEvent (PathHere, e) (SelectNode _ options) =
    let i = the Integer $ cast e
    in pure (SelectNode Nothing options, integerToFin i _)

  updateAppVal : Ctx a b c -> c -> JS_IO ()
  updateAppVal ctx z =
    do
      (MkAppState app lastV container) <- getAppState ctx
      let (newApp, async) = stepAppASync app z
      let vNew = renderApp newApp
      finalView <- runDom container (updateApp ctx) (updateNodeView lastV vNew)
      setAppState ctx (MkAppState newApp finalView container)
      setASync (updateAppVal ctx) async

  updateApp : Ctx a b c -> ViewEvent -> JS_IO ()
  updateApp ctx e =
    do
      (MkAppState app lastV container) <- getAppState ctx
      (n2, mVal) <- runDom container (updateApp ctx) (updateNodeEvent e lastV)
      case mVal of
        Nothing => setAppState ctx (MkAppState app n2 container)
        Just z =>
          do
            let (newApp, async) = stepAppInput app z
            let vNew = renderApp newApp
            finalView <- runDom container (updateApp ctx) (updateNodeView n2 vNew)
            setAppState ctx (MkAppState newApp finalView container)
            setASync (updateAppVal ctx) async


  initView : Ctx a b c -> DomNode -> View d -> JS_IO ()
  initView ctx container view =
      runDom container (updateApp ctx) (initViewDom view)

export
runApp : App a f b -> JS_IO ()
runApp {a} {f} {b} app =
  do
    bo <- body
    c1 <- appendNode' "span" bo
    c <- appendNode' "span" c1
    ctxPtr <- jscall "{}" (() -> JS_IO Ptr) ()
    let ctx = the (Ctx a f b) $ MkCtx ctxPtr
    let v = renderApp app
    let appSt = MkAppState app v c
    initView ctx c v
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
  neutral = TextNode ""

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


uniqIdView : (Int->View a) -> View a
uniqIdView x = UniqIdNode x Nothing
