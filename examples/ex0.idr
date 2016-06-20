module Main

import Js.Browser

upd : String -> String -> (String, ASync String)
upd x y = (y, never)

vw : String -> View String
vw s = textinput' ++ text s


page : App String
page = simpleApp
          ""
          vw
          upd


main : JS_IO ()
main = do
  runApp page
