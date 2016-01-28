module Main

import Js.IO

mutual
  is_even : Int -> Int
  is_even n =
      if n == 0 then 1 else is_odd $ n-1

  is_odd : Int -> Int
  is_odd n =
      if n == 0 then 0 else is_even $ n-1

main : JSIO ()
main = do
  console_log $ show $ is_even 10
