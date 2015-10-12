import Js.Browser

start : List String
start = []

upd : String -> List String -> List String
upd x y = y ++ [x]

vw : List String -> Html String
vw x = div $ [ div [textinput]
             , div (map (\x => div [text x]) x)
             ]
page : App String (List String)
page = MkApp
        start
        vw
        upd

main : JSIO ()
main = do
  runApp page

