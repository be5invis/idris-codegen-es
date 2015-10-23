import Js.Browser

vw : String -> View String
vw s = div [ textinput
           , text s
           ]

page : App String String
page = MkApp
        ""
        vw
        (\x, y => x)

main : JSIO ()
main = do
  runApp page
