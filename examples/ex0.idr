module Main

import Js.Browser
import Js.Forms

vw : Template String String
vw = div [] [textinput [onchange' id], text [] id]

pageLoop : Eff () [HTML (GuiRef String String)]
pageLoop =
  do
    x <- getInput
    update (const x)
    pageLoop

page : Eff () [HTML ()] [HTML (GuiRef String String)]
page =
  do
    initBody "" vw
    pageLoop

main : JS_IO ()
main = setASync_ $ run page
