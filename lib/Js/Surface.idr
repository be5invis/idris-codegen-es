module Js.Surface

import Js.Browser
import Data.Vect

import Debug.Trace

public export
data BtnColor = BtnRed | BtnYellow | BtnGreen | BtnBlue | BtnPrimary | BtnSecondary | BtnAccent

btnColor2css : BtnColor -> String
btnColor2css BtnRed = "btn--red"
btnColor2css BtnYellow = "btn--yello"
btnColor2css BtnGreen = "btn--green"
btnColor2css BtnBlue = "btn--blue"
btnColor2css BtnPrimary = "btn--primary"
btnColor2css BtnSecondary = "btn--secondary"
btnColor2css BtnAccent = "btn--accent"

export
btnRaised : BtnColor -> b -> String -> View b
btnRaised c v l = text "button" [click v] [css "btn--raised ", css $ btnColor2css c] l

export
tile : Attribute
tile = css "tile"

export
card : Attribute
card = css "card"

export
textinputP : String -> Maybe String -> View String
textinputP = textinputNode

export
textinputP' : String -> View String
textinputP' x = textinputNode x Nothing

export
textFormP : String -> Form String
textFormP placeholder =
  MkForm
    (Right "")
    vw
  where
    vw (Right x) = Right <$> (textinputP placeholder $ Just x)
    vw (Left _) = Right <$> textinputP' placeholder


export
tabbedApps : List Attribute -> AppGroup ts -> Vect (length ts) String ->
                App (AppGroup ts) AppGroupInputType (AppGroupAsyncType ts)
tabbedApps attrs x labels =
  MkApp
    x
    (\y => uniqIdView (\i => mkTabs attrs (renderAppGroup y) labels ("id" ++ show i) ))
    stepAppGroupInput
    stepAppGroupAsync
  where
    f2s : Fin n -> String
    f2s x = cast (finToInteger x + 1)
    checked : Bool -> List (String, String)
    checked False = []
    checked True = [("checked","true")]
    checkedFin : Fin n -> List (String, String)
    checkedFin FZ = checked True
    checkedFin _ = checked False
    mkTab : (Fin n, View a, String) -> View a
    mkTab (i, x, lbl) =
      (containerNode
        "input"
        []
        (checkedFin i ++[("type", "radio"), ("name", "tabs"),("id", "tab" ++ f2s i)])
        (t "")
      ) ++
      (containerNode
        "div"
        []
        [("class", "tab-label-content"), ("id", "tab" ++ f2s i ++ "-content")]
        ((containerNode
            "label"
            []
            [("for","tab"++f2s i)]
            (t lbl)
         ) ++ div [css "tab-content"] x
        )
      )
    mkTabs : List Attribute -> Vect n (View a) -> Vect n String -> String -> View a
    mkTabs attrs tabs labels id =
      div
        ( css ("tabs tab-" ++ id) :: attrs)
        ((concat $ map mkTab $ zip range (zip tabs labels)) ++ div [css "slide"] empty)

public export
data Menu : Nat -> Type where
  Nil : Menu 0
  (::) : String -> Menu n -> Menu (S n)

getMenuPos : String -> Menu n -> Maybe Nat
getMenuPos x y =
  getMenuPos' 0 x y
  where
    getMenuPos' : Nat -> String -> (Menu m) -> Maybe Nat
    getMenuPos' _ _ Nil = Nothing
    getMenuPos' acc y (x::xs) =
      if x == y then Just acc
        else getMenuPos' (S acc) y xs

export
runAppWithNav :  String -> AppGroup ts -> Menu (length ts) -> JS_IO()
runAppWithNav {ts} name x m =
  do
    hash <- getHash
    let s0 = case getMenuPos hash m of
                Nothing => 0
                Just z => z
    runApp'(Left <$> onHash) (MkApp (s0,x) render stpInput stpAsync)
  where
    onHash : ASync String
    onHash =
      do
        i <- onHashChange
        liftJS_IO $ getHash
    inpType : (Nat, AppGroup ts) -> Type
    inpType (_, x) = AppGroupInputType x
    renderMenu : Menu n -> View a
    renderMenu Nil = empty
    renderMenu (x::xs) = (li [] $ link [href $ "#" ++ x] x) ++ renderMenu xs
    renderAlts : Bool -> Nat -> Vect k (View a) -> View a
    renderAlts _ _ [] = empty
    renderAlts False Z (x::xs) = span [] x ++ renderAlts True Z xs
    renderAlts False (S i) (x::xs) = span [hidden] x ++ renderAlts False i xs
    renderAlts True _ (x::xs) = span [hidden] x ++ renderAlts True Z xs
    render : (s:(Nat, AppGroup ts)) -> View (inpType s)
    render (n, x) =
      (container "header" [] [css "container--baseline"] $
        (h2 [css "m--1 g--4"] name) ++
        (containerNode "input" [] [("type", "checkbox"),("id","nav--horizontal-responsive")] empty) ++
        (textNode "label" [] [("for","nav--horizontal-responsive")] "Menu")++
        ( container "nav" [] [css "g--3 nav--horizontal"] $ ul [] $
          renderMenu m
        )
      ) ++
      (renderAlts False n $ renderAppGroup x)
    stpInput : (s:(Nat, AppGroup ts)) -> inpType s ->
                  ((Nat, AppGroup ts), ASync (Either String (AppGroupAsyncType ts)))
    stpInput (n,x) y =
      let (w,z) = stepAppGroupInput x y
      in ((n,w), Right <$> z)
    stpAsync : (s:(Nat, AppGroup ts)) -> Either String (AppGroupAsyncType ts) ->
                  ((Nat, AppGroup ts), ASync (Either String (AppGroupAsyncType ts)))
    stpAsync (n, x) (Right y) =
      let (w,z) = stepAppGroupAsync x y
      in ((n,w), Right <$> z)
    stpAsync (n,x) (Left y) =
      case getMenuPos y m of
        Nothing => ((n,x), never)
        Just z => ((z,x), never)
