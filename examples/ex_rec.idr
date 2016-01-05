module Main

import Js.Browser

data TstExp = Pos Nat
            | Neg Nat
            | Plus TstExp TstExp

instance Show TstExp where
  show (Pos x) = show x
  show (Neg x) = "(-" ++ show x ++ ")"
  show (Plus x y) = "(" ++ show x ++ " + " ++ show y ++ ")"

data TstExpForms = NumberForm | PlusForm

tstForm : Lazy (Form TstExp)
tstForm =
  combine
    (selectForm ["Pos", "Neg", "Plus"])
    theNat
    theForm
  where
    theNat (Pos _) = 0
    theNat (Neg _) = 1
    theNat (Plus_) = 2
    theForm Z = formMap' (\(Pos x) => x , Pos) natForm
    theForm (S Z) = formMap' (\(Neg x) => x , Neg) natForm
    theForm _ = formMap' (\(Plus x y) => (x,y) , uncurry Plus) $ tupleForm tstForm tstForm


vw : View TstExp TstExp
vw = div $    (buildForm $ tstForm)
           .+.  dyntext .$. show


page : App TstExp TstExp
page = MkApp
        (Pos 1)
        vw
        (\x, y => (x, never))

main : JSIO ()
main = do
  runApp page
