module Js.Purecss

import Js.BrowserBase

pureButton : b -> String -> View a b
pureButton v l = addClass "pure-button" $ button v l

pureButtonActive : b -> String -> View a b
pureButtonActive v l = addClass "pure-button pure-button-active" $ pureButton v l
