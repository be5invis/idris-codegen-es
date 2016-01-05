module Main

import Js.Browser

vw : View String String
vw = div $ ii (buildForm $ textForm)
           .+. dyntext


page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
