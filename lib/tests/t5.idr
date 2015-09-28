import Js.IO


mkEvent : String -> (String,String)
mkEvent s =
  let (i, v ) = break (== '|') s
      val = strTail v
  in (i, val)


main : JSIO ()
main = do
  putStrLn $ show $ mkEvent "0|ars"
