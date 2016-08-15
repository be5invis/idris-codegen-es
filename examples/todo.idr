import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : List String -> TodoAction -> (List String, ASync TodoAction)
upd y (TodoAdd x) = (y ++ [x], never)
upd y (TodoRemove i) =  (take i y  ++ drop (i+1) y, never)

vw_todos : List (Nat, String) -> View TodoAction
vw_todos l = concat $ map (\(i,s)=> d $ button "x" (TodoRemove i) ++ t s) l

vw : List String -> View TodoAction
vw l =
  d (TodoAdd <$> buildForm' textForm) ++ vw_todos (z l)
  where
    z: List String -> List (Nat, String)
    z x = zip [0..length x] x


page : SimpleApp (List String) TodoAction
page = MkSimpleApp
        start
        never
        vw
        upd

main : JS_IO ()
main = do
  runApp page
