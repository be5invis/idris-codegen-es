import Js.ASync

data ServiceM : Type -> Type where
  PureServ : a -> ServiceM a


get_jsio : ServiceM a -> JS_IO (Either String a)
get_jsio (PureServ x) = do
  pure $ Right x


mytst : String -> ServiceM String
mytst x = PureServ $ "ola "

call_fn : (String -> JS_IO String) -> String -> JS_IO String
call_fn f x = jscall
                  "%0(%1)"
                  ((JsFn (String -> JS_IO String)) -> String -> JS_IO String)
                  (MkJsFn f)
                  x

mytstJs : String -> JS_IO String
mytstJs x = do
  r <- get_jsio $ mytst "arst"
  case r of
      Right k => pure k

tst2 : JS_IO String
tst2 = call_fn mytstJs "inputmytst"

main : JS_IO ()
main = do
  putStrLn' "start"
  r <- tst2
  putStrLn' "olare"
  putStrLn' r
