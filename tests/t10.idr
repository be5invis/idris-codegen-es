module Main

rec : Int -> Int -> Int
rec 0 y = y
rec 1 y = y
rec x y =
   rec (y-1) (x-2)

main : JS_IO ()
main = putStr' $ show $ rec 10 10
