module Main

import Js.Browser
import Js.Forms
import Effects
import Effect.State

data Input = Set
          |  Change String

Gui : Type
Gui = GuiRef String Input

vw : Template String Input
vw = div [] [form' Set [] [textinput [onchange' Change]], textF [] id]

pageLoop : Eff () [HTML Gui, STATE String]
pageLoop =
  do
    x <- getInput
    case x of
      Set =>
        do
          s <- get
          putGui s
      Change s =>
        put s
    pageLoop

page : Eff () [HTML (), STATE String] [HTML Gui, STATE String]
page =
  do
    initBody [] "" vw
    pageLoop

main : JS_IO ()
main = setASync_ $ run page
