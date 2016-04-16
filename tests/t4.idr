import Js.ASync

p : Int -> JS_IO Int
p x = do
  putStr' "ola"
  pure $ x + 1


call_fn : (Int -> JS_IO Int) -> Int -> JS_IO Int
call_fn f x =
  jscall
    "%0(%1)"
    ((JsFn (Int -> JS_IO Int)) -> Int -> JS_IO Int)
    (MkJsFn f)
    x


main : JS_IO ()
main = do
  v <- call_fn p 73
  putStrLn' $ show v
