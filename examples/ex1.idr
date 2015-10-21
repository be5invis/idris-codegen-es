import Js.Browser

page : App () String
page = MkApp
        ""
        (\x => text "ola")
        (\x, y => "")

main : JSIO ()
main = do
  runApp page
