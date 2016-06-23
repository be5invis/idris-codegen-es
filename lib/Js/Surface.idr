module Js.Surface

import Js.Browser
import Data.Vect

public export
data BtnColor = BtnRed | BtnYellow | BtnGreen | BtnBlue | BtnPrimary | BtnSecondary | BtnAccent

btnColor2css : BtnColor -> String
btnColor2css BtnRed = "btn--red"
btnColor2css BtnYellow = "btn--yello"
btnColor2css BtnGreen = "btn--green"
btnColor2css BtnBlue = "btn--blue"
btnColor2css BtnPrimary = "btn--primary"
btnColor2css BtnSecondary = "btn--secondary"
btnColor2css BtnAccent = "btn--accent"

export
btnRaised : BtnColor -> b -> String -> View b
btnRaised c v l = containerNode "button" [("click", Just v)] [("class", "btn--raised " ++ btnColor2css c)] $ text l


export
clickableTile : b -> View b -> View b
clickableTile v child = containerNode "button" [("click", Just v)] [("class", "tile")] $ child

export
clickableCard : b -> View b -> View b
clickableCard v child = containerNode "button" [("click", Just v)] [("class", "card")] $ child

export
tabbedApps : AppGroup ts -> App (AppGroup ts) AppGroupInputType (AppGroupAsyncType ts)
tabbedApps x =
  MkApp
    x
    (\y => cdiv "tabs tab-stuff" $ Prelude.Foldable.concat $ map mkTab $ zip range $ renderAppGroup y)
    stepAppGroupInput
    stepAppGroupAsync
  where
    f2s : Fin n -> String
    f2s x = cast (finToInteger x + 1)
    mkTab : (Fin n, View a) -> View a
    mkTab (i, x) =
      (containerNode
        "input"
        []
        [("type", "ratio"), ("name", "tabs"),("id", "tab" ++ f2s i)]
        (t "")
      ) ++
      (containerNode
        "div"
        []
        [("class", "tab-label-content"), ("id", "tab" ++ f2s i ++ "-content")]
        ((containerNode
            "label"
            []
            [("for","tab"++f2s i)]
            (t "xpto")
         ) ++ cdiv "tab-content" x
        )
      )

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
