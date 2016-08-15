module Main

import Js.Browser
import Data.Vect

vw : String -> View String
vw s =
  (d $ buildForm (Just $ FormSetVal s) (addSubmit "Submit" $ textForm)) ++ t s

page : SimpleApp String String
page = MkSimpleApp
        ""
        never
        vw
        (\x, y => (y, never))

main : JS_IO ()
main = do
  runApp page
