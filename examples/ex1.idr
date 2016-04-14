module Main

import Js.Browser
import Data.Vect

vw : String -> View String
vw s =
  div $ ii (buildForm $ textForm)
    <+> text s

page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
