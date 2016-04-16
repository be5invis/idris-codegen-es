import Js.ASync


tst : String
tst =
  let x = ("stra", "strb")
      (y,z) = x
  in y

main : JS_IO ()
main = do
  putStr' $ show tst
