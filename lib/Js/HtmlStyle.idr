module HtmlStyle

import Js.HtmlTemplate
import Data.Fin

%access export

public export
data Color = RGB (Fin 256) (Fin 256) (Fin 256)

data Length = MkLength String

px : Integer -> Length
px x = MkLength $ show x ++ "px"

Show Length where
  show (MkLength x) = "calc(" ++ x ++ ")"

Num Length where
  (+) (MkLength x) (MkLength y) = MkLength $ "(" ++ x ++ "+" ++ y ++ ")"
  (*) (MkLength x) (MkLength y) = MkLength $ "(" ++ x ++ "*" ++ y ++ ")"
  fromInteger = px

Show Color where
  show (RGB r g b) =
    "rgb(" ++ (show $ finToInteger r) ++ "," ++ (show $ finToInteger g) ++
      "," ++ (show $ finToInteger b) ++ ")"



height : Length -> Style
height x = MkStyle "height" (show x)

width : Length -> Style
width x = MkStyle "width" (show x)

margin : Length -> Style
margin x = MkStyle "margin" (show x)

padding : Length -> Style
padding x = MkStyle "padding" (show x)

backgroundColor : Color -> Style
backgroundColor x = MkStyle "background-color" (show x)

public export
data FlexDirection = Row | Column

private
Show FlexDirection where
  show Row = "row"
  show Column = "column"

public export
data FlexOption = Direction FlexDirection

direction : FlexDirection -> FlexOption
direction = Direction

flex : List FlexOption -> Style
flex x =
  CompStyle (MkStyle "display" "flex" :: map stlopt x)
  where
    stlopt : FlexOption -> Style
    stlopt (Direction x) = MkStyle "flex-direction" (show x)

public export
data BoxShadowOption = Blur Int
                     | HShadow Int
                     | VShadow Int

private
record BoxShadowArguments where
  constructor MkBoxShadowArguments
  hShadow : Int
  vShadow : Int
  blur : Int
  spread : Int;
  color : Color

private
boxShadowArgsToString : BoxShadowArguments -> String
boxShadowArgsToString x =
  unwords
      [(show $ hShadow x) ++ "px", (show $ vShadow x) ++ "px", (show $ blur x) ++ "px", (show $ spread x) ++ "px", show $ color x]

boxShadow : List BoxShadowOption -> Style
boxShadow x =
  MkStyle "box-shadow"
    (boxShadowArgsToString $ foldl opt (MkBoxShadowArguments 0 0 0 0 (RGB 0 0 0)) x)
  where
    opt : BoxShadowArguments -> BoxShadowOption -> BoxShadowArguments
    opt y (Blur x) = record{blur = x} y
    opt y (HShadow x) = record{hShadow = x} y
    opt y (VShadow x) = record{vShadow = x} y
