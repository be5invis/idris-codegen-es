module Main

import Js.Browser
import Data.Vect

vw : String -> View String
vw s =
  (div $ buildForm' textForm) ++ text s

page : SimpleApp String String
page = MkSimpleApp
        ""
        vw
        (\x, y => (y, never))

main : JS_IO ()
main = do
  runApp page
