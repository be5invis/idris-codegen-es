import Js.IO


ffn : Int -> JSIO Int
ffn x =
  jscall  
    "(%0 + 1)" 
    (Int -> JSIO Int)
    x

main : JSIO ()
main = do
  v <- ffn 1
  putStrLn $ show v
