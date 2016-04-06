module Main

import Js.Browser


upd : String -> String -> (String, ASync String)
upd x y = (x, never)

vw : View String String
vw = ii textinput <+> dyntext


page : App String String
page = MkApp
          ""
          vw
          upd


main : JSIO ()
main = do
  runApp page
