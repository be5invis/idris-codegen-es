module Main

plus : Int -> Int -> Int
plus x y = x + y

f : (Int -> Int -> Int) -> Int -> Int -> Int
f op x y = op x y

main : IO ()
main = print (f plus 1000 2000)