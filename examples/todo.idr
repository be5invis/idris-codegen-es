import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : TodoAction -> List String -> (List String, Maybe (ASync TodoAction))
upd (TodoAdd x) y = (y ++ [x], Nothing)
upd (TodoRemove i) y =  (take i y  ++ drop (i+1) y, Nothing)

vw_todos : View (List (Int, String)) TodoAction
vw_todos 

vw : View (List String) TodoAction
vw =
  let z = zip x [0..length x]
  in div $      (div TodoAdd <$> textinput)
           .+.. (div (map (\(x,i) => div [button (TodoRemove i) (text "x") , text x]) z))


page : App TodoAction (List String)
page = MkApp
        start
        vw
        upd

main : JSIO ()
main = do
  runApp page
