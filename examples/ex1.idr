module Main

import Js.Browser

vw : String -> View String
vw s = div [ mkform $ textForm "stuff"
           , text s
           ]

page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, Nothing))

main : JSIO ()
main = do
  runApp page
