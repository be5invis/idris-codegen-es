module Main

import Js.Browser
import Data.Vect

vw : String -> View String
vw s =
  (div $ buildForm' textForm) ++ text s

page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JS_IO ()
main = do
  runApp page
