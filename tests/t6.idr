module Main

import Js.ASync

main : JS_IO ()
main = do
  let f = the ((String,String) -> String -> (String, Maybe String ))  (\(_, s),y => (s, Just s))
  case snd $ f ("t", "tst") "cenas" of
    Just z => putStr' z
