module Js.BrowserApp

import Js.ASync
import public Js.BrowserDom
import public Js.Typeable
import Js.BrowserTemplate


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
          Template a f ->
          ((x:a) -> f x -> AppM b a) ->
          (a -> b -> AppM b a) ->
          App a f b

data AppState : (a:Type) -> Type where
  MkAppState : (x: a) ->
               TemplateState a ->
               AppState a

appStateState : AppState a -> a
appStateState (MkAppState z _ ) = z

export
stepAppASync : App a f b -> a -> b -> AppM b a
stepAppASync (MkApp x1 x2 x3 x4) x y = x4 x y

export
stepAppInput : App a f b -> (x: a) -> f x -> AppM b a
stepAppInput (MkApp x1 x2 x3 x4) x y = x3 x y


export
getTemplate : App a f b -> Template a f
getTemplate (MkApp _ t _ _) = t


export
getInit : App a f b -> AppM b a
getInit (MkApp x _ _ _) = x

getAppStateState : Ctx (AppState a) -> JS_IO a
getAppStateState ctx = appStateState <$> getCtx ctx

mutual
  runAndSetAppM : App a f b -> Ctx (AppState a) -> AppM b a -> JS_IO a
  runAndSetAppM app ctx x = runAppM (setASync (updateAppVal app ctx) ) x


  updateAppVal : App a f b -> Ctx (AppState a) -> b -> JS_IO ()
  updateAppVal app ctx z =
    do
      (MkAppState st templateSt) <- getCtx ctx
      newSt <- runAndSetAppM app ctx $ stepAppASync app st z
      newTemplateSt <- updateTemplate newSt templateSt
      setCtx ctx (MkAppState newSt newTemplateSt)


  updateApp : App a f b -> Ctx (AppState a) -> (x:a) -> f x -> JS_IO ()
  updateApp app ctx st e =
    do
      (MkAppState _ templateSt) <- getCtx ctx
      newSt <- runAndSetAppM app ctx $ stepAppInput app st e
      newTemplateSt <- updateTemplate newSt templateSt
      setCtx ctx (MkAppState newSt newTemplateSt)

export
runApp : App a f b -> JS_IO ()
runApp {a} {f} {b} app =
  do
    c <- body
    --ctxPtr <- jscall "{}" (() -> JS_IO Ptr) ()
    --let ctx = the (Ctx a) $ MkCtx ctxPtr
    ctx <- makeCtx (believe_me 0)
    st <- runAndSetAppM app ctx $ getInit app
    templateSt <- initTemplate c st (getAppStateState ctx) (updateApp app ctx) (getTemplate app)
    let appSt = MkAppState st templateSt
    setCtx ctx $ appSt
