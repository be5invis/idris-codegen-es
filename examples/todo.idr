import Js.Browser

start : List String
start = []

data TodoAction = TodoAdd String
                | TodoRemove Nat

upd : List String -> TodoAction -> AppM TodoAction (List String)
upd y (TodoAdd x) = pure $ y ++ [x]
upd y (TodoRemove i) =  pure $ take i y  ++ drop (i+1) y

vw_todos : List (Nat, String) -> View TodoAction
vw_todos l = concat $ map (\(i,s)=> d $ button "x" (TodoRemove i) ++ t s) l

vw : List String -> View TodoAction
vw l =
  d (TodoAdd <$> buildForm' textForm) ++ vw_todos (z l)
  where
    z: List String -> List (Nat, String)
    z x = zip [0..length x] x


page : SimpleApp (List String) TodoAction
page = mkSimpleApp
        (pure start)
        vw
        upd

main : JS_IO ()
main = do
  runApp page
