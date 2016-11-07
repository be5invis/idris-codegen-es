module Main

import Js.Browser
import Js.Forms

upd : String -> String -> AppM String String
upd x y = pure y

vw : STemplate String String
--vw = div [] [bform [sonchange id] textform, dyntext [] id]
vw = div [] [textinput [sonchange id, dynsetval (const $ Just "ola")], dyntext [] id]

page : SimpleApp String String
page = mkSimpleApp
          (pure "")
          vw
          upd


main : JS_IO ()
main = do
  runApp page
