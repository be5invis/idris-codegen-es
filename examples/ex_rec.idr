module Main

import Js.Browser
import Data.Vect

data TstExp = Pos Nat
            | Neg Nat
            | Plus TstExp TstExp

Show TstExp where
  show (Pos x) = show x
  show (Neg x) = "(-" ++ show x ++ ")"
  show (Plus x y) = "(" ++ show x ++ " + " ++ show y ++ ")"

data TstExpForms = NumberForm | PlusForm

indentV : Nat -> View a b -> View a b
indentV i x = div $ t (pack $ the (List Char) $ replicate i '-') .+. x

indentF : Nat -> Form a -> Form a
indentF i = vtrans (indentV i)

tstForm : Nat -> Lazy (Form TstExp)
tstForm i =
  indentF i $ combine
    (selectForm ["Pos", "Neg", "Plus"])
    theNat
    theForm
  where
    theNat (Pos _) = 0
    theNat (Neg _) = 1
    theNat (Plus_) = 2
    theForm FZ = formMap' (\(Pos x) => x , Pos) $ natForm
    theForm (FS FZ) = formMap' (\(Neg x) => x , Neg) natForm
    theForm _ = formMap' (\(Plus x y) => (x,y) , uncurry Plus) $ tupleForm (tstForm $ i+1) (tstForm $ i+1)


vw : View TstExp TstExp
vw = div $    (buildForm $ tstForm 0)
           .+.  div (dyntext .$. show)


page : App TstExp TstExp
page = MkApp
        (Pos 1)
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
