module Js.BrowserUtils

import Js.BrowserBase


public
text : String -> View Void b
text = static dyntext

public
button : (a, String) -> View Void a
button = static dynbtn

public
listView : View a b -> View (List a) b
listView v =
  dynView $ r
  where
    r [] = empty
    r (x::xs) = static v x .+. r xs


public
dynViewMaybe : (a->View Void b) -> View (Maybe a) b
dynViewMaybe r =
  dynView r2
  where
    r2 Nothing = empty
    r2 (Just x) = r x


public
chainView : View a b -> View (Either a b) c -> View a c
chainView x y =
  foldView
    updEvt
    updInp
    Nothing
    (Left <$> x .?. s2a .+. Right <$> y .?. id)
  where
    s2a : Maybe (Either a b) -> Maybe a
    s2a (Just (Left x)) = Just x
    s2a _ = Nothing
    updEvt : Either b c -> Maybe (Either a b) -> (Maybe (Either a b), Maybe c)
    updEvt (Left x) _ = (Just $ Right x, Nothing)
    updEvt (Right x) _ = (Nothing, Just x)
    updInp : a -> Maybe (Either a b) -> Maybe (Either a b)
    updInp x _ = Just $ Left x
