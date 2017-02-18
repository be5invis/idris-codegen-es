import Js.Browser
import Js.Forms
import Effects

data TodoAction : Nat -> Type where
  TodoAdd : String -> TodoAction n
  TodoRemove : Fin n -> TodoAction n


vw : Template Nat (\n=> Vect n String) (\n=>TodoAction n)
vw = div [] [ bform [onsubmit (\_,_,x => TodoAdd x)] textform
            , vectOnDivIndex [] id (\_,x=>x) (div [] [button [onclick (\_,x => TodoRemove $ fst x)] "x", textD [] (\(_**(_,s))=>s)])
            ]

Gui : Nat -> Type
Gui = GuiRef Nat (\n=>Vect n String) TodoAction

lenAfterAction : (n : Nat) -> TodoAction n -> Nat
lenAfterAction n (TodoAdd _) = S n
lenAfterAction (S n) (TodoRemove _) = n

procAct : (a:TodoAction n) -> Eff () [HTML (Gui n)] [HTML (Gui (lenAfterAction n a))]
procAct {n} (TodoAdd s) =
  updateGuiM (s::)
procAct {n=S m} (TodoRemove i) =
  updateGuiM (deleteAt i)

pageLoop : Eff () [HTML (Gui n)] [HTML (Gui m)]
pageLoop =
  do
    x <- getInput
    procAct x
    pageLoop

page : Eff () [HTML ()] [HTML (Gui 0)]
page =
  do
    initBodyM [] [] vw
    pageLoop

main : JS_IO ()
main = setASync_ $ run page
