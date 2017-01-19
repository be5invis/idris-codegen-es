module SVG

import Js.Browser

svgNS : String
svgNS = "http://www.w3.org/2000/svg"

export
data CircleOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  CircleStringOption : String -> Dyn (DPair a f) String -> CircleOption a f g

export
data RectOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  RectStringOption : String -> Dyn (DPair a f) String -> RectOption a f g

export
data SVGElemD : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  Circle : List (CircleOption a f g) -> SVGElemD a f g
  Rect : List (RectOption a f g) -> SVGElemD a f g

doubleToString : Double -> String
doubleToString = show

namespace Simple
  public export
  SVGElem : {t:Type} -> Type -> Type -> Type
  SVGElem {t} b c = SVGElemD t (const b) (const c)

namespace Circle
  export
  circle : List (CircleOption a f g) -> SVGElemD a f g
  circle = Circle

  export
  r : IDyn d (DPair a f) Double => d -> CircleOption a f g
  r x = CircleStringOption "r" (map doubleToString $ getDyn x)

  export
  cx : IDyn d (DPair a f) Double => d -> CircleOption a f g
  cx x = CircleStringOption "cx" (map doubleToString $ getDyn x)

  export
  cy : IDyn d (DPair a f) Double => d -> CircleOption a f g
  cy x = CircleStringOption "cy" (map doubleToString $ getDyn x)

namespace Rect
  export
  rect : List (RectOption a f g) -> SVGElemD a f g
  rect = Rect

  export
  x : IDyn d (DPair a f) Double => d -> RectOption a f g
  x p = RectStringOption "x" (map doubleToString $ getDyn p)

  export
  y : IDyn d (DPair a f) Double => d -> RectOption a f g
  y p = RectStringOption "y" (map doubleToString $ getDyn p)

  export
  width : IDyn d (DPair a f) Double => d -> RectOption a f g
  width p = RectStringOption "width" (map doubleToString $ getDyn p)

  export
  height : IDyn d (DPair a f) Double => d -> RectOption a f g
  height p = RectStringOption "height" (map doubleToString $ getDyn p)

  export
  fill :  IDyn d (DPair a f) String => d -> RectOption a f g
  fill p = RectStringOption "fill" (getDyn p)

circleOptToAttr : CircleOption a f g -> Attribute a f g
circleOptToAttr (CircleStringOption n v) = StrAttribute n v

rectOptToAttr : RectOption a f g -> Attribute a f g
rectOptToAttr (RectStringOption n v) = StrAttribute n v

svgToTempl : SVGElemD a f g -> Template a f g
svgToTempl (Circle opts) =
  customNodeNS svgNS "circle" (map circleOptToAttr opts) []
svgToTempl (Rect opts) =
  customNodeNS svgNS "rect" (map rectOptToAttr opts) []

export
svg : List (Attribute a f g) -> List (SVGElemD a f g) -> Template a f g
svg attrs childs =
  customNodeNS svgNS "svg" attrs
    (map svgToTempl childs)
