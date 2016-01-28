import Js.IO

p : Int -> Int
p x = x + 1


call_fn : (Int -> Int) -> Int -> JSIO Int
call_fn f x =
  jscall
    "%0(%1)"
    ((Int -> Int) -> Int -> JSIO Int)
    f x

main : JSIO ()
main = do
  v <- call_fn p 1
  putStrLn' $ show v
