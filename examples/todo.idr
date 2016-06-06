import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : TodoAction -> List String -> (List String, ASync TodoAction)
upd (TodoAdd x) y = (y ++ [x], never)
upd (TodoRemove i) y =  (take i y  ++ drop (i+1) y, never)

vw_todos : List (Nat, String) -> View TodoAction
vw_todos l = concat $ map (\(i,t)=> button "x" (TodoRemove i) ++ text t) l

vw : List String -> View TodoAction
vw l =
  div (TodoAdd <$> buildForm' textForm) ++ vw_todos (z l)
  where
    z: List String -> List (Nat, String)
    z x = zip [0..length x] x


page : App TodoAction (List String)
page = MkApp
        start
        vw
        upd

main : JS_IO ()
main = do
  runApp page
