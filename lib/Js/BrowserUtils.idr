module Js.BrowserUtils

import Js.BrowserBase
import Js.IO

public
static : View a b -> a -> View Void b
static vw x = ii $ init vw x

public
dynbtn : View (a, String) a
dynbtn = dynView (\(x,y) => button x y )

public
dyntext : View String a
dyntext = dynView t

public
listView : View a b -> View (List a) b
listView v =
  dynView $ r
  where
    r [] = empty
    r (x::xs) = static v x .+. r xs

public
merge : List (View a b) -> View a b
merge (x::xs) = x .+. merge xs
merge []      = empty


public
dynViewMaybe : (a->View Void b) -> View (Maybe a) b
dynViewMaybe r =
  dynView r2
  where
    r2 Nothing = empty
    r2 (Just x) = r x


public
chainView : View (Either a b) c -> View a b -> View a c
chainView f x =
  foldView
    updEvt
    updInp
    Nothing
    (Left <$> x .?. s2a .+. Right <$> f .?. id)
  where
    s2a : Maybe (Either a b) -> Maybe a
    s2a (Just (Left x)) = Just x
    s2a _ = Nothing
    updEvt : Either b c -> Maybe (Either a b) -> (Maybe (Either a b), Maybe c)
    updEvt (Left x) _ = (Just $ Right x, Nothing)
    updEvt (Right x) _ = (Nothing, Just x)
    updInp : a -> Maybe (Either a b) -> Maybe (Either a b)
    updInp x _ = Just $ Left x

public
chainViewS : View a c -> View a a -> View a c
chainViewS f x =
  chainView (f .$. pinput) x
  where
    pinput (Right x) = x
    pinput (Left x) = x

public
viewApp : View a b -> App () ()
viewApp vw =
  MkApp
    ()
    (ii $ io vw)
    (\x, y => ((), never))
