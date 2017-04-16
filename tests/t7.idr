module Main


mutual
  %inline
  is_even : Int -> Int
  is_even n =
      if n == 0 then 1 else is_odd $ n-1

  is_odd : Int -> Int
  is_odd n =
      if n == 0 then 0 else is_even $ n-1

main : JS_IO ()
main = do
  putStr' $ show $ is_even 100001
