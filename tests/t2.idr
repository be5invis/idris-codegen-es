import Js.ASync

ffn : Int -> JS_IO Int
ffn x =
  jscall
    "(%0 + 1)"
    (Int -> JS_IO Int)
    x

main : JS_IO ()
main = do
  v <- ffn 1
  putStrLn' $ show v
