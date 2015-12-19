import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : TodoAction -> List String -> (List String, ASync TodoAction)
upd (TodoAdd x) y = (y ++ [x], never)
upd (TodoRemove i) y =  (take i y  ++ drop (i+1) y, never)

vw_todos : View (List (Nat, String)) TodoAction
vw_todos = listView $ div $ dynbtn .$. (\(i, _) => (TodoRemove i,"x")) ..+.. dyntext .$. snd

vw : View (List String) TodoAction
vw =
  div $ (TodoAdd <$> (buildForm $ textForm "task"))
        .+.. vw_todos .$. z
  where
    z: List String -> List (Nat, String)
    z x = zip [0..length x] x


page : App TodoAction (List String)
page = MkApp
        start
        vw
        upd

main : JSIO ()
main = do
  runApp page
