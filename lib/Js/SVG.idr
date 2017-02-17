module SVG

import Js.Browser

svgNS : String
svgNS = "http://www.w3.org/2000/svg"

xlinkNS : String
xlinkNS = "http://www.w3.org/1999/xlink"

export
interface ShapeOption (o:(a:Type) -> (f:a->Type) -> (g:a->Type) -> Type) where
  shapeAttribute : (a:Type) -> (f:a->Type) -> (g:a->Type) -> Attribute a f g -> o a f g

export
data CircleOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkCircleOption : Attribute a f g -> CircleOption a f g

export
data RectOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkRectOption : Attribute a f g -> RectOption a f g

export
data ImageOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkImageOption : Attribute a f g -> ImageOption a f g

export
data TextOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkTextOption : Attribute a f g -> TextOption a f g

export
ShapeOption RectOption where
  shapeAttribute _ _ _ x = MkRectOption x

export
ShapeOption ImageOption where
  shapeAttribute _ _ _ x = MkImageOption x

export
ShapeOption CircleOption where
  shapeAttribute _ _ _ x = MkCircleOption x

export
ShapeOption TextOption where
  shapeAttribute _ _ _ x = MkTextOption x

export
data GOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkGOption : Attribute a f g -> GOption a f g

export
data SVGElemD : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  CMapElem : ((x:a) -> h x -> f x) -> SVGElemD a f g -> SVGElemD a h g
  Circle : List (CircleOption a f g) -> SVGElemD a f g
  Rect : List (RectOption a f g) -> SVGElemD a f g
  Image : List (ImageOption a f g) -> Dyn (DPair a f) String -> SVGElemD a f g
  G : List (GOption a f g) ->
        ((x:a) -> f x -> List (h x)) ->
              SVGElemD a h g -> SVGElemD a f g
  SG : List (GOption a f g) ->
        List (SVGElemD a f g) -> SVGElemD a f g
  Text : List (TextOption a f g) -> Dyn (DPair a f) String -> SVGElemD a f g

namespace Dependent
  export
  (>$<) : ((x:a) -> h x -> f x) -> SVGElemD a f g -> SVGElemD a h g
  (>$<) = CMapElem

namespace Simple
  public export
  SVGElem : {t:Type} -> Type -> Type -> Type
  SVGElem {t} b c = SVGElemD t (const b) (const c)

  export
  (>$<) : {t:Type} -> (c -> b) -> SVGElemD t (const b) (const d) -> SVGElemD t (const c) (const d)
  (>$<) fn = CMapElem (\_=>fn)

namespace Circle
  export
  circle : List (CircleOption a f g) -> SVGElemD a f g
  circle = Circle

  export
  r : IDyn d (DPair a f) Double => d -> CircleOption a f g
  r x = MkCircleOption $ customStrAttr "r" (map doubleToString $ getDyn x)

  export
  cx : IDyn d (DPair a f) Double => d -> CircleOption a f g
  cx x = MkCircleOption $ customStrAttr "cx" (map doubleToString $ getDyn x)

  export
  cy : IDyn d (DPair a f) Double => d -> CircleOption a f g
  cy x = MkCircleOption $ customStrAttr "cy" (map doubleToString $ getDyn x)

namespace Rect
  export
  rect : List (RectOption a f g) -> SVGElemD a f g
  rect = Rect

  export
  x : IDyn d (DPair a f) Double => d -> RectOption a f g
  x p = MkRectOption $ customStrAttr "x" (map doubleToString $ getDyn p)

  export
  y : IDyn d (DPair a f) Double => d -> RectOption a f g
  y p = MkRectOption $ customStrAttr "y" (map doubleToString $ getDyn p)

  export
  width : IDyn d (DPair a f) Double => d -> RectOption a f g
  width p = MkRectOption $ customStrAttr "width" (map doubleToString $ getDyn p)

  export
  height : IDyn d (DPair a f) Double => d -> RectOption a f g
  height p = MkRectOption $ customStrAttr "height" (map doubleToString $ getDyn p)

namespace Image
  export
  image : IDyn s (DPair a f) String => List (ImageOption a f g) -> s -> SVGElemD a f g
  image opts s = Image opts (getDyn s)

  export
  x : IDyn d (DPair a f) Double => d -> ImageOption a f g
  x p = MkImageOption $ customStrAttr "x" (map doubleToString $ getDyn p)

  export
  y : IDyn d (DPair a f) Double => d -> ImageOption a f g
  y p = MkImageOption $ customStrAttr "y" (map doubleToString $ getDyn p)

  export
  width : IDyn d (DPair a f) Double => d -> ImageOption a f g
  width p = MkImageOption $ customStrAttr "width" (map doubleToString $ getDyn p)

  export
  height : IDyn d (DPair a f) Double => d -> ImageOption a f g
  height p = MkImageOption $ customStrAttr "height" (map doubleToString $ getDyn p)

namespace Text
  export
  text : IDyn txt (DPair a f) String => List (TextOption a f g) -> txt -> SVGElemD a f g
  text opts t = Text opts (getDyn t)

  export
  x : IDyn d (DPair a f) Double => d -> TextOption a f g
  x p = MkTextOption $ customStrAttr "x" (map doubleToString $ getDyn p)

  export
  y : IDyn d (DPair a f) Double => d -> TextOption a f g
  y p = MkTextOption $ customStrAttr "y" (map doubleToString $ getDyn p)



export
fill :  (IDyn d (DPair a f) String, ShapeOption o) => d -> o a f g
fill {a} {f} {g} p = shapeAttribute a f g $ CSSAttribute "fill" (getDyn p)

export
transform : ShapeOption o => Dyn (DPair a f) Transform -> o a f g
transform {a} {f} {g} t = shapeAttribute a f g $ transform t

export
onclickD : ShapeOption o => ((x:a) -> f x -> g x) -> o a f g
onclickD {a} {f} {g} fn = shapeAttribute a f g $ EventClick fn

export
onclick : ShapeOption o => {t:Type} -> (b -> c) -> o t (const b) (const c)
onclick {t} {b} {c} fn = shapeAttribute t (const b) (const c) $ EventClick (\_=>fn)

namespace Group
  export
  gD : List (GOption a f g) ->
        ((x:a) -> f x -> List (h x)) ->
              SVGElemD a h g -> SVGElemD a f g
  gD = G

  export
  g : {t:Type} -> List (GOption t (const b) (const c)) ->
        (b -> List d) ->
              SVGElemD t (const d) (const c) -> SVGElemD t (const b) (const c)
  g o f e = G o (\_,z=>f z) e

export
sG :  List (GOption a f g) -> List (SVGElemD a f g) -> SVGElemD a f g
sG = SG

circleOptToAttr : CircleOption a f g -> Attribute a f g
circleOptToAttr (MkCircleOption x) = x

rectOptToAttr : RectOption a f g -> Attribute a f g
rectOptToAttr (MkRectOption x) = x

imageOptToAttr : ImageOption a f g -> Attribute a f g
imageOptToAttr (MkImageOption x) = x

gOptToAttr : GOption a f g -> Attribute a f g
gOptToAttr (MkGOption x) = x

textOptToAttr : TextOption a f g -> Attribute a f g
textOptToAttr (MkTextOption x) = x

covering
svgToTempl : SVGElemD a f g -> Template a f g
svgToTempl (CMapElem f x) =
  f >$< svgToTempl x
svgToTempl (Circle opts) =
  customNodeNS svgNS "circle" (map circleOptToAttr opts) []
svgToTempl (Rect opts) =
  customNodeNS svgNS "rect" (map rectOptToAttr opts) []
svgToTempl (Image opts url) =
  customNodeNS svgNS "image" (customStrAttrNS xlinkNS "xlink:href" url :: map imageOptToAttr opts) []
svgToTempl (G opts fn childT) =
  listCustomNS svgNS "g" (map gOptToAttr opts) fn (svgToTempl childT)
svgToTempl (SG opts childs) =
  customNodeNS svgNS "g" (map gOptToAttr opts) (map svgToTempl childs)
svgToTempl (Text opts str) =
  customTextNS svgNS "text" (map textOptToAttr opts) str

export
svg : List (Attribute a f g) -> List (SVGElemD a f g) -> Template a f g
svg attrs childs =
  customNodeNS svgNS "svg" attrs
    (map svgToTempl childs)
