module Main

import Js.Browser
import Data.Vect

vw : String -> View String
vw s =
  (div $ buildForm' textForm) ++ text s

page : App String
page = simpleApp
        ""
        vw
        (\x, y => (y, never))

main : JS_IO ()
main = do
  runApp page
