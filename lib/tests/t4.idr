import Js.IO

p : Int -> JSIO Int
p x = do
  putStr "ola"
  pure $ x + 1


call_fn : (Int -> JSIO Int) -> Int -> JSIO Int
call_fn f x =
  jscall  
    "%0(%1)" 
    ((Int -> JSIO Int) -> Int -> JSIO Int)
    f x


main : JSIO ()
main = do
  v <- call_fn p 73
  putStrLn $ show v
