module Js.BrowserBase

import Js.ASync
import public Data.Vect
import public Js.BrowserDom

Path : Type
Path = List Nat

ViewEvent : Type
ViewEvent = (Path, String)

mutual
  data ViewNode : Type -> Type where
    MkViewNode : String -> Bool -> b -> (Dom String ()) ->
                    (String -> b -> Dom String (b, Maybe a)) ->
                      (Vect n (View a)) -> (Vect n DomPath) -> ViewNode a

  export
  data View a = MkView (List (ViewNode a))


export
Semigroup (View a) where
  (<+>) (MkView a) (MkView b) = MkView $ a ++ b

export
Monoid (View a) where
  neutral = MkView []


export
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

data NodeMatch a = Match Nat (ViewNode a, ViewNode a)
                 | NewNode (ViewNode a)
                 | DeleteNode Nat

matchNodes : Nat -> List (ViewNode a) -> List (ViewNode a) -> List (NodeMatch a)
matchNodes pos (x::xs) (y::ys) = Match pos (x, y) :: matchNodes (pos + 1) xs ys
matchNodes pos [] (y::ys) = NewNode y :: matchNodes (pos + 1) [] ys
matchNodes pos (x::xs) [] = DeleteNode pos :: matchNodes (pos + 1) xs []
matchNodes pos [] [] = []

mutual
  updateViewNode : ViewEvent -> Path -> Ctx a b -> DomNode -> ViewNode a -> JS_IO (ViewNode a, Maybe a)
  updateViewNode ([], e) p ctx container (MkViewNode tag override st ini upd childs pos) =
    do
      (newst, ma) <- runDom container (updateApp ctx p) $ upd e st
      pure (MkViewNode tag override newst ini upd childs pos, ma)

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


  diffUpdateViewNode : Ctx a b -> DomNode -> Path -> (ViewNode a, ViewNode a) -> JS_IO (ViewNode a)
  diffUpdateViewNode {a} {b} ctx container path (MkViewNode {n=no} ot oo os oi ou oc op, MkViewNode {n} t o s i u c p) =
    case exactLength no c of
      Just nc =>
        if ot == t && not o then
          do
            newChilds <- sequence $ map
                            diffUpdateChild
                            (the (Vect no (Fin no, DomPath, View a, View a)) $ range `zip` (op `zip` (oc `zip` nc)))
            pure $ MkViewNode ot oo os oi ou newChilds op
        else initNew
      Nothing => initNew
    where
      diffUpdateChild : (Fin z, DomPath, View a, View a) -> JS_IO (View a)
      diffUpdateChild (pos, dpath, vold, vnew) =
        case solvePath dpath container of
          Just ncont => diffUpdateView ctx ncont (path ++ [finToNat pos]) (vold, vnew)
      initNew : JS_IO (ViewNode a)
      initNew =
        do
          clear' container
          runDom container (updateApp ctx path) i
          pure $ MkViewNode t o s i u c p


    --case decEq (no, ot) (n, t) of
    --  _ =>

  diffUpdateView : Ctx a b -> DomNode -> Path -> (View a, View a) -> JS_IO (View a)
  diffUpdateView ctx container path (MkView lo, MkView ln) =
    MkView <$> (sequence $ map updateMatch $ reverse $ matchNodes 0 lo ln)
    where
      updateMatch (Match pos m) =
        do
          c <- child' pos container
          case c of
            Just newContainer => diffUpdateViewNode ctx newContainer (path++[pos]) m


  updateApp : Ctx a b -> Path -> String -> JS_IO ()
  updateApp ctx p e =
    do
      appSt <- getAppState ctx
      (view2, mVal) <- updateView (p,e) [] ctx (container appSt) (lastView appSt)
      case mVal of
        Nothing => setAppState ctx (record{lastView=view2} appSt)
        Just x => pure()

  initView : Path -> Ctx a b -> DomNode -> View a -> JS_IO ()
  initView path ctx container (MkView v) =
    do
      sequence $
        map
          (initViewNode ctx container)
          (zip (map (\z=> path ++ [z]) $ [0..length v]) v)
      pure ()

  initViewNode : Ctx a b -> DomNode -> (Path, ViewNode a) -> JS_IO ()
  initViewNode ctx container (path, MkViewNode _ _ _ ini _ _ _) =
    do
      c <- appendNode' "span" container
      runDom c (updateApp ctx path) ini
      pure ()


startApp : Ctx a b -> App a b -> DomNode -> JS_IO ()
startApp ctx x container =
  do
    let v = render x $ state x
    initView [] ctx container v
    setAppState ctx $ MkAppState x v container


export
runApp : App a b -> JS_IO ()
runApp {a} {b} app =
  do
    bo <- body
    ctx <- jscall "{}" (() -> JS_IO Ptr) ()
    startApp (the (Ctx a b) $ MkCtx ctx) app bo

export
mkView : String -> Bool -> b -> (Dom String ()) ->
            (String -> b -> Dom String (b, Maybe a)) ->
              Vect n (View a) -> Vect n DomPath -> View a
mkView tag override state draw update childs slots = MkView [MkViewNode tag override state draw update childs slots]
