import Js.IO

export
data ServiceM : Type -> Type where
  PureServ : a -> ServiceM a


get_jsio : ServiceM a -> JSIO (Either String a)
get_jsio (PureServ x) = do
  pure $ Right x

export
mytst : String -> ServiceM String
mytst x = PureServ $ "ola "

call_fn : (String -> JSIO String) -> String -> JSIO String
call_fn f x = jscall
                  "%0(%1)"
                  ((String -> JSIO String) -> String -> JSIO String)
                  f x

mytstJs : String -> JSIO String
mytstJs x = do
  r <- get_jsio $ mytst "arst"
  case r of
      Right k => pure k

tst2 : JSIO String
tst2 = call_fn mytstJs "inputmytst"

export
main : JSIO ()
main = do
  putStrLn' "start"
  r <- tst2
  putStrLn' "olare"
  putStrLn' r
