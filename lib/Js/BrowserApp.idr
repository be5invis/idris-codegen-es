module Js.BrowserApp

import Js.ASync
import public Js.BrowserDom
import public Js.Typeable
import public Js.BrowserTemplate


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
data App : Type -> Type -> Type where
  MkApp : AppM b a ->
          Template a b ->
          (a -> b -> AppM b a) ->
          App a b

data AppState : (a:Type) -> Type where
  MkAppState : (x: a) ->
               TemplateState a ->
               AppState a

appStateState : AppState a -> a
appStateState (MkAppState z _ ) = z


export
stepApp : App a b -> a -> b -> AppM b a
stepApp (MkApp x1 x2 x3) x y = x3 x y


export
getTemplate : App a b -> Template a b
getTemplate (MkApp _ t _) = t


export
getInit : App a b -> AppM b a
getInit (MkApp x _ _) = x

getAppStateState : Ctx (AppState a) -> JS_IO a
getAppStateState ctx = appStateState <$> getCtx ctx

mutual
  runAndSetAppM : App a b -> Ctx (AppState a) -> AppM b a -> JS_IO a
  runAndSetAppM app ctx x = runAppM (setASync (updateApp app ctx) ) x

  updateApp : App a b -> Ctx (AppState a) -> b -> JS_IO ()
  updateApp app ctx e =
    do
      (MkAppState st templateSt) <- getCtx ctx
      newSt <- runAndSetAppM app ctx $ stepApp app st e
      newTemplateSt <- updateTemplate newSt templateSt
      setCtx ctx (MkAppState newSt newTemplateSt)

export
runApp : App a b -> JS_IO ()
runApp app =
  do
    c <- body
    ctx <- makeCtx (believe_me 0)
    st <- runAndSetAppM app ctx $ getInit app
    templateSt <- initTemplate c st (getAppStateState ctx) (updateApp app ctx) (getTemplate app)
    let appSt = MkAppState st templateSt
    setCtx ctx $ appSt
