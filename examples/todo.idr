import Js.Browser
import Js.Forms


data TodoAction = TodoAdd String
                | TodoRemove Nat


vw : Template (List String) TodoAction
vw = div [] [ bform [onchange' TodoAdd] textform
            , listOnDivIndex [] id (div [] [button [onclick (TodoRemove . fst)] "x", text [] Prelude.Basics.snd])
            ]

Gui : Type
Gui = GuiRef (List String) TodoAction

pageLoop : Eff () [HTML Gui]
pageLoop =
  do
    x <- getInput
    case x of
      TodoAdd z => update (z::)
      TodoRemove i => update (\y=>take i y  ++ drop (i+1) y)
    pageLoop

page : Eff () [HTML ()] [HTML Gui]
page =
  do
    initBody [] vw
    pageLoop

main : JS_IO ()
main = setASync_ $ run page
