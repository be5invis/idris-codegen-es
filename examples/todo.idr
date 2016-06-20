import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : List String -> TodoAction -> (List String, ASync TodoAction)
upd y (TodoAdd x) = (y ++ [x], never)
upd y (TodoRemove i) =  (take i y  ++ drop (i+1) y, never)

vw_todos : List (Nat, String) -> View TodoAction
vw_todos l = concat $ map (\(i,t)=> div $ button "x" (TodoRemove i) ++ text t) l

vw : List String -> View TodoAction
vw l =
  div (TodoAdd <$> buildForm' textForm) ++ vw_todos (z l)
  where
    z: List String -> List (Nat, String)
    z x = zip [0..length x] x


page : App TodoAction
page = simpleApp
        start
        vw
        upd

main : JS_IO ()
main = do
  runApp page
