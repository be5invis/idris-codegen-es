import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : TodoAction -> List String -> List String
upd (TodoAdd x) y = y ++ [x]
upd (TodoRemove i) y =  take i y  ++ drop (i+1) y

vw : List String -> Html TodoAction
vw x = 
  let z = zip x [0..length x]
  in div $ [ div [TodoAdd <$> textinput]
             , div (map (\(x,i) => div [button (TodoRemove i) (text "x") , text x]) z)
             ]
page : App TodoAction (List String)
page = MkApp
        start
        vw
        upd

main : JSIO ()
main = do
  runApp page

