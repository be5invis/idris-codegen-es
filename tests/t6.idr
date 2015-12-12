module Main

import Js.IO

main : JSIO ()
main = do
  let f = the ((String,String) -> String -> (String, Maybe String ))  (\(_, s),y => (s, Just s))
  case snd $ f ("t", "tst") "cenas" of
    Just z => jsdebug z
