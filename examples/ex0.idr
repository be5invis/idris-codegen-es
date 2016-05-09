module Main

import Js.Browser


upd : String -> String -> (String, ASync String)
upd x y = (x, never)

vw : String -> View String
vw s = textinput <+> text s


page : App String String
page = MkApp
          ""
          vw
          upd


main : JS_IO ()
main = do
  runApp page
