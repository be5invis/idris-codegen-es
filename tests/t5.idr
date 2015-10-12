import Js.IO


tst : String
tst =
  let x = ("stra", "strb")
      (y,z) = x
  in y

main : JSIO ()
main = do
  putStr $ show tst
