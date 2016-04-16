import Js.ASync

p : Int -> Int
p x = x + 1


call_fn : (Int -> Int) -> Int -> JS_IO Int
call_fn f x =
  jscall
    "%0(%1)"
    ((JsFn (Int -> Int)) -> Int -> JS_IO Int)
    (MkJsFn f)
    x

main : JS_IO ()
main = do
  v <- call_fn p 1
  putStrLn' $ show v
