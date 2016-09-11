module Main

import Js.Browser

upd : String -> String -> AppM String String
upd x y = pure y

vw : String -> View String
vw s = textinput' ++ t s


page : SimpleApp String String
page = mkSimpleApp
          (pure "")
          vw
          upd


main : JS_IO ()
main = do
  runApp page
