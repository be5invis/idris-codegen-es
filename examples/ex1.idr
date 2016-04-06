module Main

import Js.Browser
import Data.Vect

vw : View String String
vw =
  div $ ii (buildForm $ textForm)
    <+> dyntext
    <+> (ii $ dyntext .$. (show . finToInteger) `chainViewS` selectinput ["0","1","3"]  )
    <+> (ii $ dyntext .$. (show . finToInteger) `chainViewS` (buildForm $ selectForm ["0","1","3"]  ))
    <+> (ii $ dyntext `chainViewS` ( ii $ (\(x,y) => show x ++ show y) <$> (buildForm $ tupleForm natForm natForm))  )
    <+> (ii $ dyntext `chainViewS` ( ii $ (\x => show x ) <$> (buildForm $ natForm))  )



page : App String String
page = MkApp
        ""
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
