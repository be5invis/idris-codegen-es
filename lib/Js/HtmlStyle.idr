module HtmlStyle

import Js.HtmlTemplate
import Js.HtmlUtils
import Data.Fin

%access export

height : IDyn d (DPair a f) Double => d -> Attribute a f g
height x = CSSAttribute "height" (doubleToString <$> getDyn x)

width : IDyn d (DPair a f) Double => d -> Attribute a f g
width x = CSSAttribute "width" (doubleToString <$> getDyn x)

margin :IDyn d (DPair a f) Double => d -> Attribute a f g
margin x = CSSAttribute "margin" (doubleToString <$> getDyn x)

padding : IDyn d (DPair a f) Double => d -> Attribute a f g
padding x = CSSAttribute "padding" (doubleToString <$> getDyn x)

backgroundColor : IDyn s (DPair a f) String => s -> Attribute a f g
backgroundColor x = CSSAttribute "background-color" (getDyn x)


public export
data FlexDirection = Row | Column

flexDirectionToString : FlexDirection -> String
flexDirectionToString Row = "row"
flexDirectionToString Column = "column"

export
data FlexOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkFlexOption : Attribute a f g -> FlexOption a f g

export
direction : IDyn d (DPair a f) FlexDirection => d -> FlexOption a f g
direction x = MkFlexOption $ CSSAttribute "flex-direction" (flexDirectionToString <$> getDyn x)

private
flexOptToAttr : FlexOption a f g -> Attribute a f g
flexOptToAttr (MkFlexOption x) = x

flex : List (FlexOption a f g) -> Attribute a f g
flex x =
  GroupAttribute $ CSSAttribute "display" (pure "flex") :: map flexOptToAttr x -- CSSAttribute  dir]


data BoxShadowOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  Blur : Dyn (DPair a f) Double -> BoxShadowOption a f g
  HShadow : Dyn (DPair a f) Double -> BoxShadowOption a f g
  VShadow : Dyn (DPair a f) Double -> BoxShadowOption a f g

blur : IDyn d (DPair a f) Double => d -> BoxShadowOption a f g
blur x = Blur $ getDyn x

hShadow : IDyn d (DPair a f) Double => d -> BoxShadowOption a f g
hShadow x = HShadow $ getDyn x

vShadow : IDyn d (DPair a f) Double => d -> BoxShadowOption a f g
vShadow x = VShadow $ getDyn x

private
record BoxShadowArguments (a:Type) (f : a->Type) where
  constructor MkBoxShadowArguments
  hShadow : Dyn (DPair a f) Double
  vShadow : Dyn (DPair a f) Double
  blur : Dyn (DPair a f) Double
  spread : Dyn (DPair a f) Double
  color : Dyn (DPair a f) String

private
boxShadowOptionsToArgs : List (BoxShadowOption a f g) -> BoxShadowArguments a f
boxShadowOptionsToArgs x =
  foldl opt (MkBoxShadowArguments (pure 0) (pure 0) (pure 0) (pure 0) (pure "black")) x
  where
    opt : BoxShadowArguments a f -> BoxShadowOption a f g -> BoxShadowArguments a f
    opt y (Blur x) = record{blur = getDyn x} y
    opt y (HShadow x) = record{hShadow = getDyn x} y
    opt y (VShadow x) = record{vShadow = getDyn x} y

private
boxShadowArgsToString : Double -> Double -> Double -> Double -> String -> String
boxShadowArgsToString hsh vsh blr spr clr =
  unwords
      [(show hsh) ++ "px", (show vsh) ++ "px", (show blr) ++ "px", (show spr) ++ "px", clr]

boxShadow :  List (BoxShadowOption a f g) -> Attribute a f g
boxShadow {a} {f} x =
  CSSAttribute "box-shadow" (boxShadowArgsToString <$> hShadow args <*> vShadow args <*> blur args <*> spread args <*> color args)
  where
    args : BoxShadowArguments a f
    args = boxShadowOptionsToArgs x

data Transform = MkTransform String

translate : Double -> Double -> Transform
translate x y =
  MkTransform $ "translate(" ++ show x ++ "px," ++ show y ++ "px)"

transform : IDyn t (DPair a f) Transform => t -> Attribute a f g
transform x = CSSAttribute "transform" ((\(MkTransform z) => z) <$> getDyn x)
