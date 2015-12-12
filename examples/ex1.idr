module Main

import Js.Browser

vw : View String String
vw = div $    (buildForm $ textForm "stuff")
           .+.. dyntext


page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
