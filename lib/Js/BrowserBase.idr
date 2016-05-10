module Js.BrowserBase

import Js.ASync
import public Data.Vect
import public Js.BrowserDom
import public Js.SimpleData

Path : Type
Path = List Nat

ViewEvent : Type
ViewEvent = (Path, String)

ViewNodeTag : Type
ViewNodeTag = (Nat, String, SDataTy)

total
viewStateType : ViewNodeTag -> Type
viewStateType (_, _ , st) = iSDataTy st

mutual

  record ViewNode (t:ViewNodeTag) a where
    constructor MkViewNode
    state : viewStateType t
    init : Dom String ()
    update : viewStateType t -> Dom String (viewStateType t)
    updateEvent : String -> viewStateType t -> Dom String (viewStateType t, Maybe a)
    childs : Vect (fst t) (View a)
    childsPaths : Vect (fst t) DomPath

  ViewNodeSigma : Type -> Type
  ViewNodeSigma a = (t:ViewNodeTag ** ViewNode t a)

  export
  data View a = MkView (List (ViewNodeSigma a))


export
Semigroup (View a) where
  (<+>) (MkView a) (MkView b) = MkView $ a ++ b

export
Monoid (View a) where
  neutral = MkView []


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

data NodeMatch a = MatchNode Nat (t:ViewNodeTag ** (ViewNode t a, ViewNode t a))
                 | ReplaceNode Nat (ViewNodeSigma a )
                 | NewNode (ViewNodeSigma a)
                 | DeleteNode Nat


matchNodes : Nat -> (t1: ViewNodeTag) -> (t2: ViewNodeTag) ->
                Dec (t1 = t2) -> ViewNode t1 a -> ViewNode t2 a -> NodeMatch a
matchNodes k t1 t1 (Yes Refl) y z = MatchNode k (t1 ** (y,z))
matchNodes k t1 t2 (No contra) y z = ReplaceNode k (t2 ** z)


matchNodesList : Nat -> List (ViewNodeSigma a) -> List (ViewNodeSigma a) -> List (NodeMatch a)
matchNodesList pos ((t1**x)::xs) ((t2**y)::ys) = (matchNodes pos t1 t2 (decEq t1 t2) x y) :: matchNodesList (pos + 1) xs ys
matchNodesList pos [] (y::ys) = NewNode y :: matchNodesList (pos + 1) [] ys
matchNodesList pos (x::xs) [] = DeleteNode pos :: matchNodesList (pos + 1) xs []
matchNodesList pos [] [] = []

mutual
  updateViewNode : ViewEvent -> Path -> Ctx a b -> DomNode -> ViewNodeSigma a -> JS_IO (ViewNodeSigma a, Maybe a)
  updateViewNode ([], e) p ctx container (t**v) =
    do
      (newst, ma) <- runDom container (updateApp ctx p) $ (updateEvent v) e (state v)
      let newV = MkViewNode newst (init v) (update v) (updateEvent v) (childs v) (childsPaths v)
      pure ((t ** newV ), ma)

  updateView : ViewEvent -> Path -> Ctx a b -> DomNode -> View a -> JS_IO (View a, Maybe a)
  updateView (t::r, e) p ctx container (MkView l) =
    do
      let (b,v::a) = splitAt t l
      let pos = length b
      c <- child' pos container
      case c of
        Just cContainer =>
          do
            (nview, out) <- updateViewNode (r,e) (p ++ [pos]) ctx cContainer v
            pure (MkView $ b ++ (nview::a), out)
        Nothing => pure (MkView l, Nothing)


{-  diffUpdateViewNode {a} {b} ctx container path
      initNew : JS_IO (ViewNode a)
      initNew =
        do
          clear' container
          runDom container (updateApp ctx path) i
          pure $ MkViewNode typ t o s i u c p
-}

  diffUpdateEqNodes : Ctx a b -> DomNode -> Path -> ViewNode t a -> ViewNode t a -> JS_IO (ViewNode t a)
  diffUpdateEqNodes ctx container path x y =
    do
      newChilds <- diffUpdateChilds (childsPaths x) (childs x) (childs y)
      newSt <- runDom container (updateApp ctx path) $ (update y) (state x)
      pure $ MkViewNode newSt (init x) (update x) (updateEvent x) newChilds (childsPaths x)
    where
      diffUpdateChild : (Fin z, DomPath, View a, View a) -> JS_IO (View a)
      diffUpdateChild (pos, dpath, vold, vnew) =
        case !(solvePath dpath container) of
          Just ncont => diffUpdateView ctx ncont (path ++ [finToNat pos]) (vold, vnew)
      diffUpdateChilds : Vect k DomPath -> Vect k (View a) -> Vect k (View a) -> JS_IO (Vect k (View a))
      diffUpdateChilds op oc nc =
        sequence $ map
            diffUpdateChild
            (range `zip` (op `zip` (oc `zip` nc)))

  diffUpdateView : Ctx a b -> DomNode -> Path -> (View a, View a) -> JS_IO (View a)
  diffUpdateView ctx container path (MkView lo, MkView ln) =
    MkView <$> (sequence $ map updateMatch $ reverse $ matchNodesList 0 lo ln)
    where
      updateMatch (MatchNode pos (t ** (v1,v2))) =
        do
          c <- child' pos container
          case c of
            Just newContainer =>
              do
                vr <- diffUpdateEqNodes ctx newContainer (path++[pos]) v1 v2
                pure (t ** vr)

  updateAppVal : Ctx a b -> a -> JS_IO ()
  updateAppVal ctx x =
    do
      appSt <- getAppState ctx
      let app = theApp appSt
      let (newS, async) = (update app) x (state app)
      finalView <- diffUpdateView ctx (container appSt) [] (lastView appSt, (render app) newS)
      setAppState ctx (record{lastView = finalView, theApp = record{state = newS} app} appSt)
      setASync (updateAppVal ctx) async

  updateApp : Ctx a b -> Path -> String -> JS_IO ()
  updateApp ctx p e =
    do
      appSt <- getAppState ctx
      (view2, mVal) <- updateView (p,e) [] ctx (container appSt) (lastView appSt)
      setAppState ctx (record{lastView=view2} appSt)
      case mVal of
        Nothing => pure ()
        Just x => updateAppVal ctx x


  initView : Path -> Ctx a b -> DomNode -> View a -> JS_IO (View a)
  initView path ctx container (MkView v) =
    do
      newV <- sequence $
                  map
                    (initViewNode ctx container)
                    (zip (map (\z=> path ++ [z]) $ [0..length v]) v)
      pure $ MkView newV

  initViewNode : Ctx a b -> DomNode -> (Path, ViewNodeSigma a) -> JS_IO (ViewNodeSigma a)
  initViewNode ctx container (path, (t ** v) ) =
    do
      c <- appendNode' "span" container
      runDom c (updateApp ctx path) (init v)
      newSt <- runDom c (updateApp ctx path) $ (update v) (state v)
      newChilds <- sequence $ map (initView path ctx container) (childs v)
      pure $ (t ** MkViewNode newSt (init v) (update v) (updateEvent v) newChilds (childsPaths v))


startApp : Ctx a b -> App a b -> DomNode -> JS_IO ()
startApp ctx x container =
  do
    let v = render x $ state x
    v2 <- initView [] ctx container v
    setAppState ctx $ MkAppState x v2 container


export
runApp : App a b -> JS_IO ()
runApp {a} {b} app =
  do
    bo <- body
    c <- appendNode' "span" bo
    ctx <- jscall "{}" (() -> JS_IO Ptr) ()
    startApp (the (Ctx a b) $ MkCtx ctx) app c

export
leafView : (s:String) -> (b:SDataTy) -> iSDataTy b ->
              Dom String () -> (iSDataTy b -> Dom String (iSDataTy b)) ->
                (String -> iSDataTy b -> Dom String (iSDataTy b, Maybe a)) -> View a
leafView {a} s b st0 i u ue =
  MkView [((Z, s, b) ** MkViewNode st0 i u ue [] [])]


export
mkView : (s:String) -> (b:SDataTy) -> iSDataTy b ->
              Dom String () -> (iSDataTy b -> Dom String (iSDataTy b)) ->
                (String -> iSDataTy b -> Dom String (iSDataTy b, Maybe a)) ->
                  Vect n (View a) -> Vect n DomPath -> View a
mkView {n} {a} s b st0 i u ue c cp =
  MkView [((n, s, b) ** MkViewNode st0 i u ue c cp)]
