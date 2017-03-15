module HtmlStyle

import Js.HtmlTemplate
import Js.HtmlUtils
import Data.Fin

%access export

private
pixels : Double -> String
pixels x = show x ++ "px"

height : Double -> Attribute a f g
height x = CSSAttribute "height" (DynConst $ pixels x)

heightF : (a->Double) -> Attribute a b
heightF f = CSSAttribute "height" (DynA $ \(_**x) => pixels $ f x)

width : Double -> Attribute a f g
width x = CSSAttribute "width" (DynConst $ pixels x)

widthF : (a->Double) -> Attribute a b
widthF f = CSSAttribute "width" (DynA $ \(_**x) => pixels $ f x)

margin : Double -> Attribute a f g
margin x = CSSAttribute "margin" (DynConst $ pixels x)

padding : Double -> Attribute a f g
padding x = CSSAttribute "padding" (DynConst $ pixels x)

backgroundColor : String -> Attribute a f g
backgroundColor x = CSSAttribute "background-color" (DynConst x)

backgroundColorF : (a->String) -> Attribute a b
backgroundColorF f = CSSAttribute "background-color" (DynA $ \(_**x)=>f x)


public export
data FlexDirection = Row | Column

flexDirectionToString : FlexDirection -> String
flexDirectionToString Row = "row"
flexDirectionToString Column = "column"

export
data FlexOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkFlexOption : Attribute a f g -> FlexOption a f g

export
direction : FlexDirection -> FlexOption a f g
direction x = MkFlexOption $ CSSAttribute "flex-direction" (DynConst $ flexDirectionToString x)

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

blur : Double -> BoxShadowOption a f g
blur x = Blur $ DynConst x

hShadow : Double -> BoxShadowOption a f g
hShadow x = HShadow $ DynConst x

vShadow : Double -> BoxShadowOption a f g
vShadow x = VShadow $ DynConst x

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
    opt y (Blur x) = record{blur = x} y
    opt y (HShadow x) = record{hShadow = x} y
    opt y (VShadow x) = record{vShadow = x} y

private
boxShadowArgsToString : Double -> Double -> Double -> Double -> String -> String
boxShadowArgsToString hsh vsh blr spr clr =
  unwords
      [pixels hsh, pixels vsh, pixels blr, pixels spr, clr]

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

transform : Transform -> Attribute a f g
transform (MkTransform x) = CSSAttribute "transform" (DynConst x) -- ((\(MkTransform z) => z) <$> getDyn x)

transformF : (a->Transform) -> Attribute a b
transformF f = CSSAttribute "transform" (DynA $ \(_**x) => let (MkTransform z) = f x in z) -- ((\(MkTransform z) => z) <$> getDyn x)

public export
data Position = Static | Fixed Double Double

position : Position -> Attribute a f g
position Static =
  CSSAttribute "position" (DynConst "static")
position (Fixed x y) =
  groupAttribute [ CSSAttribute "position" (DynConst "fixed")
                 , CSSAttribute "left" (DynConst $ pixels x)
                 , CSSAttribute "top" (DynConst $ pixels x)]

zIndex : Int -> Attribute a f g
zIndex x = CSSAttribute "z-index" (DynConst $ show x)

namespace UserSelect

  public export
  data UserSelectType = Auto | None | Text | All

  userSelect : UserSelectType -> Attribute a f g
  userSelect Auto = CSSAttribute "user-select" $ DynConst "auto"
  userSelect None = CSSAttribute "user-select" $ DynConst "none"
  userSelect Text = CSSAttribute "user-select" $ DynConst "text"
  userSelect All = CSSAttribute "user-select" $ DynConst "all"
