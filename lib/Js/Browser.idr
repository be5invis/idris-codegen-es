module Js.Browser

import Data.SortedSet
import public Js.IO

union : Ord a => SortedSet a -> SortedSet a -> SortedSet a
union x y = fromList $ SortedSet.toList x ++ SortedSet.toList y

%include js "Js/browser_lib_b.js"


debug : a -> JSIO ()
debug x = jscall "debug(%0)" (Ptr -> JSIO ()) (believe_me x)

abstract
data Widget = MkWidget String 
                       (List (String, String)) 
                       (List Widget)
                       (List (String, String))
             | MkText String

abstract
data BrowserEvent = BEvent String String


abstract
data React : Type -> Type where
  ReactAsyncAction : JSIO () -> React ()
  ReactId : React String
  ReactRaw : String -> React (Maybe String)
  ReactFn : (a -> b) -> React a -> React b
  ReactConst : a -> React a
  ReactApp : React (a -> b) -> React a -> React b
  ReactBind : React a -> (a -> React b) -> React b
  ReactFoldPast : (a -> s -> s) -> s -> React a -> React s


record ReactStGlobal where
  constructor MkReactStGlobal
  idcount : Integer
  actions : JSIO ()

data CReact a = MkCReact b 
                         (SortedSet String)
                         (Maybe a) 
                         (BrowserEvent -> (ReactStGlobal, b)
                                -> (a, (ReactStGlobal, b, SortedSet String)) )


getDeps : CReact k -> SortedSet String
getDeps (MkCReact _ x _ _) = x

step_reactRaw : SortedSet String -> String -> (BrowserEvent -> (ReactStGlobal, (Maybe String))
                              -> (Maybe String, (ReactStGlobal, (Maybe String), SortedSet String )) )
step_reactRaw d x (BEvent si z) (sg, sl) =
 if x == si then
  (Just z, (sg,  Just z, d))
  else (sl, (sg, sl, d))

mutual

  cmp : React a -> CReact a
  cmp ReactId =
      MkCReact () empty Nothing
               (\x, (sg, s) => (show $ idcount sg, ( record{idcount = idcount sg + 1} sg, s, empty)))
  cmp (ReactConst x) = MkCReact () empty Nothing (\y,(z1,z2) => (x,(z1, z2, empty)))
  cmp (ReactRaw i)  =
    let d = insert i $ empty
    in MkCReact Nothing d Nothing
                               (step_reactRaw d i)
  cmp (ReactAsyncAction a) =
      MkCReact () empty Nothing
               (\_, (g,s) => ((),(record{actions=actions g >>= (\_ => a)} g, s, empty)))
  cmp (ReactFn f r) = 
      let (MkCReact s deps _ fr) = cmp r
      in MkCReact s deps Nothing (\x, s => let (y,s2) = fr x s in (f y, s2)) 
  cmp (ReactApp r1 r2) =
      let cr1 = cmp r1
          cr2 = cmp r2
          d   = union (getDeps cr1) (getDeps cr2)
      in MkCReact (cr1, cr2) d Nothing (stp_app d)  
      where
          stp_app d x (sg, (s1, s2)) = 
              let (z1, (sg', s1')) = step x (sg, s1)
                  (z2, (sg'', s2')) = step x (sg', s2)
                  d   = union (getDeps s1') (getDeps s2')
              in (z1 z2, (sg'', (s1', s2'), d))
  cmp (ReactBind x f) =
      let cx = cmp x
          d  = getDeps cx
      in MkCReact (cx, Nothing) d Nothing (stp_bind f)

  stp_bind : (z -> React y) -> BrowserEvent -> (ReactStGlobal, (CReact z, Maybe (CReact y) )) -> 
                       (y, (ReactStGlobal, (CReact z, Maybe (CReact y) ), SortedSet String )) 
  stp_bind f x@(BEvent ke vl) (sg, (sx, sf)) =
    case sf of
         Nothing => stp_bind_newx f x (sg, sx)
         Just sf' =>
            if contains ke (getDeps sx) then stp_bind_newx f x (sg, sx)
              else let (z, (sg', sf'')) = step x (sg, sf')
                   in  (z, (sg', (sx, Just sf''), union (getDeps sx) (getDeps sf'')  ))
                              
    where
      stp_bind_newx : (z -> React y) -> BrowserEvent -> (ReactStGlobal, CReact z) ->
                        (y, (ReactStGlobal, (CReact z, Maybe (CReact y) ), SortedSet String )) 
      stp_bind_newx g x (sg, sx) =
          let (z1, (sg', sx')) = step x (sg, sx)
              sf'              = cmp (g z1)
              (z2, (sg'', sf')) = step x (sg, sf')
          in  (z2, (sg, (sx', Just sf'), union (getDeps sx') (getDeps sf') ) )


  step : BrowserEvent -> (ReactStGlobal, CReact a) ->
                          (a, (ReactStGlobal, CReact a))
  step x@(BEvent ke vl) z@(sg, MkCReact _ deps last_val _) =
    case last_val of
      Nothing => step_calc x z
      Just lstv =>
         if contains ke deps then step_calc x z
            else (lstv, z)
    where
      step_calc : BrowserEvent -> (ReactStGlobal, CReact a) ->
                          (a, (ReactStGlobal, CReact a))
      step_calc xc z@(sgc, MkCReact slc depsc last_valc stpc) =    
        let (r, (sg_next, sl_next, d_next)) = stpc xc (sgc, slc)
        in (r, (sg_next, MkCReact sl_next d_next (Just r) stpc) )


instance Functor React where
  map f x = ReactFn f x
  
instance Applicative React where
  pure x = ReactConst x
  f <*> x = ReactApp f x

instance Monad React where
  x >>= f = ReactBind x f

js_create_array : List (JSIO Ptr) -> JSIO Ptr
js_create_array [] = jscall "[]" (JSIO Ptr)
js_create_array (h::r) = do
  ph <- h
  pr <- js_create_array r
  jscall "[%0].concat(%1)" (Ptr -> Ptr -> JSIO Ptr) ph pr

render : Widget -> JSIO Ptr
render (MkText s) = jscall "b$node('span', {}, %0)" (String -> JSIO Ptr) s
render (MkWidget tag props childs callbacks) = do
    childs' <- js_create_array $ map render childs
    props' <- mk_props props
    callbacks' <- mk_props callbacks
    jscall "b$node(%0, %1, %2, %3)" (String -> Ptr -> Ptr -> Ptr -> JSIO Ptr) tag props' childs' callbacks'
  where
    mk_key_prop : (String, String) -> JSIO Ptr
    mk_key_prop (s, p) = jscall "[%0, %1]" (String -> String -> JSIO Ptr) s p

    mk_props : List (String, String) -> JSIO Ptr
    mk_props x = do
      lprops <- (js_create_array $ map mk_key_prop x)
      jscall "b$list2obj(%0)" (Ptr -> JSIO Ptr) lprops
 

setDisplay : Widget -> JSIO ()
setDisplay e = do
  r <- render e 
  jscall "b$setDisplay(%0)" (Ptr -> JSIO ()) r

setR :  (ReactStGlobal, CReact Widget) -> JSIO ()
setR x = jscall "b$currentReact=%0" (Ptr -> JSIO ()) (believe_me x)

getR : JSIO (ReactStGlobal, CReact Widget)
getR = believe_me $ jscall "b$currentReact" (() -> JSIO Ptr) ()

stepR : BrowserEvent -> JSIO ()
stepR x = do
  r <- getR
  let (a, (g,rc)) = step x r
  setDisplay a
  actions g
  setR (record{actions = pure ()} g,rc)

mkEvent : String -> BrowserEvent
mkEvent s =
  let (i, v ) = break (== '|') s
      val = strTail v
  in BEvent i val

bstepR : String -> JSIO ()
bstepR a = do
  stepR $ mkEvent a 

set_stepR : JSIO ()
set_stepR = jscall "b$stepr_i = %0" ( (String -> JSIO ()) -> JSIO () ) (bstepR)

public
runReact : React Widget -> JSIO ()
runReact x = do
  setR (MkReactStGlobal 0 (pure ()) , cmp x)
  set_stepR
  stepR (BEvent "" "") 
------ signal primitives ------



------ assync primitives ------

public
data AsyncResult a =  Running
                    | Error String
                    | Result a

instance Functor AsyncResult where
  map f x = case x of
                 Result y => Result $ f y
                 Running => Running
                 Error s => Error s

instance Applicative AsyncResult where
  pure x = Result x
  f <*> v = case f of
                 Result f' => map f' v
                 Running => Running
                 Error s => Error s


instance Monad AsyncResult where
  x >>= f = case x of
                 Result y => f y
                 Running => Running
                 Error s => Error s

public
post_request : String -> String -> React (AsyncResult String)
post_request url req = do
  i <- ReactId
  ReactAsyncAction $ jscall 
                      "b$post_request(%0, %1, %2)" 
                      (String -> String -> String -> JSIO ()) 
                      url 
                      i 
                      req
  ms <- ReactRaw i
  case ms of
       Nothing => pure Running
       Just s => pure $ Result s
{-
public
post_json : String -> JsonValue -> React (AsyncResult JsonValue)
post_json url req =
  pjson <$> post_request url (show req)
  where
    pjson : AsyncResult String -> AsyncResult JsonValue
    pjson x = do
      y <- x
      case parse jsonToplevelValue y of
        Right v => pure v
        Left e => Error e
        -}
------ graphic pimitives ------

public  
plainText : String -> Widget
plainText x = MkText x


public
table : List (List Widget) -> Widget
table x = 
  MkWidget "table" [] (map mkrow x) []
  where
    mkrow : List Widget -> Widget
    mkrow x = MkWidget "tr" [] (map (\y => MkWidget "td" [] [y] []) x) []

public
vflow : List Widget -> Widget
vflow x = table $ map (\y => [y]) x

public
hflow : List Widget -> Widget
hflow x = table $ [x]

------ input primitives -------

public
inputText : React (Widget, String)
inputText = 
  do
    i <- ReactId
    ms <- ReactRaw i
    pure $ (inp (bprops i) callbacks, fromMaybe "" ms) 
  where
    inp : List (String, String) -> List (String, String) -> Widget
    inp p c = MkWidget "input" p [] c -- props  [] [] -- callbacks

    bprops : String -> List (String, String)
    bprops i = [("type", "text"), ("id", i)]
    
    callbacks : List (String, String)
    callbacks = [("onchange", "b$valChange")]
