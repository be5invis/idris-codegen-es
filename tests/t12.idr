module Main

range : Int
range = 1000

testProg : Int -> Int
testProg n = loop n
where
	lmt : Int
	lmt = min (n + 100) range

	loop : Int -> Int
	loop i = if i >= lmt then i else loop (i + 1)

main : IO()
main = printLn $ testProg 0