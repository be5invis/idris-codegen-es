module HtmlStyle

import Js.HtmlTemplate
import Data.Fin

%access export


height : Double -> Style
height x = MkStyle "height" (show x)

width : Double -> Style
width x = MkStyle "width" (show x)

margin : Double -> Style
margin x = MkStyle "margin" (show x)

padding : Double -> Style
padding x = MkStyle "padding" (show x)

backgroundColor : String -> Style
backgroundColor x = MkStyle "background-color" x

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
  color : String

private
boxShadowArgsToString : BoxShadowArguments -> String
boxShadowArgsToString x =
  unwords
      [(show $ hShadow x) ++ "px", (show $ vShadow x) ++ "px", (show $ blur x) ++ "px", (show $ spread x) ++ "px", color x]

boxShadow : List BoxShadowOption -> Style
boxShadow x =
  MkStyle "box-shadow"
    (boxShadowArgsToString $ foldl opt (MkBoxShadowArguments 0 0 0 0 "black") x)
  where
    opt : BoxShadowArguments -> BoxShadowOption -> BoxShadowArguments
    opt y (Blur x) = record{blur = x} y
    opt y (HShadow x) = record{hShadow = x} y
    opt y (VShadow x) = record{vShadow = x} y
