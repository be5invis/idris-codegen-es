module Main

rec : Int -> Int -> Int
rec 0 y = y
rec 1 y = y
rec x y =
   rec (y-1) (x-2)

f : (Int -> Int -> Int) -> Int -> Int -> Int
f op x y = op x y

main : IO ()
main = do
	fn <- pure rec
	print (f fn 10 5)