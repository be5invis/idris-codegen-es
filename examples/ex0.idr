module Main

import Js.Browser


upd : String -> String -> (String, ASync String)
upd x y = (x, never)

vw : String -> View String
vw s = textinput' <+> text s <+> text "ola"


page : App String String
page = MkApp
          ""
          vw
          upd


main : JSIO ()
main = do
  runApp page
