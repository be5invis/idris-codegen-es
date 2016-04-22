module Js.BrowserBase

import Js.ASync
import public Data.Vect
import public Js.BrowserDom

{-
data Path = Here
          | PathFst Path
          | PathSnd Path

Eq Path where
  Here        == Here        = True
  (PathFst x) == (PathFst y) = x == y
  (PathSnd x) == (PathSnd y) = x == y
  _           == _           = False
-}

Path : Type
Path = List Nat

ViewEvent : Type
ViewEvent = (Path, String)

mutual
  export
  record ViewNode a where
    constructor MkViewNode
    tag : String
    override : Bool
    state : b
    init : Dom String (Vect n DomPath)
    update : String -> b -> Dom String (b, Maybe a)
    child : Vect n (View a)


  export
  data View a = MkView (List (ViewNode a))

export
Semigroup (View a) where
  (<+>) (MkView a) (MkView b) = MkView $ a ++ b

export
Monoid (View a) where
  neutral = MkView []

{-
proc_event_view : DomNode -> (ViewEvent -> JS_IO) -> ViewEvent -> ViewNode a -> JS_IO (ViewNode a, Maybe a)
proc_event_view container proc ([],e) v =
  do
    newSt <- runDom container proc $ (update v) e (state v)
  record {
  } v
-}


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

updateApp : Ctx a b -> ViewEvent -> JS_IO ()
updateApp ctx (p, x) =
  do
    putStr' x

mutual
  initView : Path -> Ctx a b -> DomNode -> (a -> JS_IO ()) -> View a -> JS_IO ()
  initView path ctx container proc (MkView v) =
    do
      sequence $
        map
          (initViewNode ctx container proc)
          (zip (map (\z=> path ++ [z]) $ [0..length v]) v)
      pure ()

  initViewNode : Ctx a b -> DomNode -> (a -> JS_IO ()) -> (Path, ViewNode a) -> JS_IO ()
  initViewNode ctx container proc (path, x) =
    do
      runDom container (\y=> updateApp ctx (path, y)) (init x)
      pure ()


startApp : Ctx a b -> App a b -> DomNode -> JS_IO ()
startApp ctx x container =
  do
    let v = render x $ state x
    initView [] ctx container (\_=>pure ()) v
    setAppState ctx $ MkAppState x v container


export
runApp : App a b -> JS_IO ()
runApp {a} {b} app =
  do
    bo <- body
    ctx <- jscall "{}" (() -> JS_IO Ptr) ()
    startApp (the (Ctx a b) $ MkCtx ctx) app bo

export
mkView : String -> Bool -> b -> (Dom String (Vect n DomPath)) ->
            (String -> b -> Dom String (b, Maybe a)) -> Vect n (View a) -> View a
mkView tag override state draw update childs = MkView [MkViewNode tag override state draw update childs]
