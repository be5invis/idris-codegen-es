module Main

import Js.Browser
import Data.Vect

vw : View String String
vw =
  div $ ii (buildForm $ textForm)
    .+. dyntext
    .+. (ii $ dyntext .$. (show . finToInteger) `chainViewS` selectinput ["0","1","3"]  )



page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
