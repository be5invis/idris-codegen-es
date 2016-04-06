module Js.Surface

import Js.BrowserBase
import Data.Vect

data BtnColor = BtnRed | BtnYellow | BtnGreen | BtnBlue | BtnPrimary | BtnSecondary | BtnAccent

btnColor2css : BtnColor -> String
btnColor2css BtnRed = "btn-red"
btnColor2css BtnYellow = "btn-yello"
btnColor2css BtnGreen = "btn-green"
btnColor2css BtnBlue = "btn-blue"
btnColor2css BtnPrimary = "btn-primary"
btnColor2css BtnSecondary = "btn-secondary"
btnColor2css BtnAccent = "btn-accent"

public
btnRaised : BtnColor -> b -> String -> View a b
btnRaised c v l =
  addClass ("btn-raised" ++ btnColor2css c) $ button v l

{-
navigation : String -> List (String, b, List (String, b) ) -> View Void b
navigation title items =

  where
    dropItem (lvl val) = li $ a val lbl
    item (lbl, val, drop) =
      if isNil drop then
        li $ a val lbl
        else li $ a val lbl .+. (map dropItem drop)
    menu = ul $

    list = zip [0..length lst] lst
    menu = addClass "pure-menu pure-menu-horizontal" div $ addClass "pure-menu-list" $ ul $
              map (\i, lbl, _ => addClass "pure-menu-item" $ li $ addClass "pure-menu-link" $ a i lbl ) list
    render x = index x


hMenu : Vect n (String, View a b) -> View a b
hMenu lst =
  where
    list = zip [0..length lst] lst
    menu = addClass "pure-menu pure-menu-horizontal" div $ addClass "pure-menu-list" $ ul $
              map (\i, lbl, _ => addClass "pure-menu-item" $ li $ addClass "pure-menu-link" $ a i lbl ) list
    render x = index x
-}
