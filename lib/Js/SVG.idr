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
data BCircleOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkCircleOption : Attribute a f g -> BCircleOption a f g

export
data BRectOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkRectOption : Attribute a f g -> BRectOption a f g

export
data BImageOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkImageOption : Attribute a f g -> BImageOption a f g

export
data BTextOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkTextOption : Attribute a f g -> BTextOption a f g


export
ShapeOption BRectOption where
  shapeAttribute _ _ _ x = MkRectOption x

export
ShapeOption BImageOption where
  shapeAttribute _ _ _ x = MkImageOption x

export
ShapeOption BCircleOption where
  shapeAttribute _ _ _ x = MkCircleOption x

export
ShapeOption BTextOption where
  shapeAttribute _ _ _ x = MkTextOption x


export
data BGOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  MkGOption : Attribute a f g -> BGOption a f g

export
data BSVGElem : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  CMapElem : ((x:a) -> h x -> f x) -> BSVGElem a f g -> BSVGElem a h g
  Circle : List (BCircleOption a f g) -> BSVGElem a f g
  Rect : List (BRectOption a f g) -> BSVGElem a f g
  Image : List (BImageOption a f g) -> Dyn (DPair a f) String -> BSVGElem a f g
  G : List (BGOption a f g) ->
        ((x:a) -> f x -> List (h x)) ->
              BSVGElem a h g -> BSVGElem a f g
  SG : List (BGOption a f g) ->
        List (BSVGElem a f g) -> BSVGElem a f g
  Text : List (BTextOption a f g) -> Dyn (DPair a f) String -> BSVGElem a f g

namespace Dependent

  public export
  SVGElem : (a:Type) -> (a->Type) -> (a->Type) -> Type
  SVGElem = BSVGElem

  public export
  CircleOption : (a:Type) -> (a->Type) -> (a->Type) -> Type
  CircleOption = BCircleOption

  public export
  RectOption : (a:Type) -> (a->Type) -> (a->Type) -> Type
  RectOption = BRectOption

  public export
  ImageOption : (a:Type) -> (a->Type) -> (a->Type) -> Type
  ImageOption = BImageOption

  public export
  TextOption : (a:Type) -> (a->Type) -> (a->Type) -> Type
  TextOption = BTextOption

  public export
  GOption : (a:Type) -> (a->Type) -> (a->Type) -> Type
  GOption = BGOption

  export
  (>$<) : ((x:a) -> h x -> f x) -> BSVGElem a f g -> BSVGElem a h g
  (>$<) = CMapElem

namespace Simple
  public export
  SVGElem : {t:Type} -> Type -> Type -> Type
  SVGElem {t} b c = BSVGElem t (const b) (const c)

  public export
  CircleOption : {t:Type} -> Type -> Type -> Type
  CircleOption {t} b c = BCircleOption t (const b) (const c)

  public export
  RectOption : {t:Type} -> Type -> Type -> Type
  RectOption {t} b c = BRectOption t (const b) (const c)

  public export
  ImageOption : {t:Type} -> Type -> Type -> Type
  ImageOption {t} b c = BImageOption t (const b) (const c)

  public export
  TextOption : {t:Type} -> Type -> Type -> Type
  TextOption {t} b c = BTextOption t (const b) (const c)

  public export
  GOption : {t:Type} -> Type -> Type -> Type
  GOption {t} b c = BGOption t (const b) (const c)

  export
  (>$<) : {t:Type} -> (c -> b) -> BSVGElem t (const b) (const d) -> BSVGElem t (const c) (const d)
  (>$<) fn = CMapElem (\_=>fn)

namespace Circle
  export
  circle : List (CircleOption a f g) -> SVGElem a f g
  circle = Circle

  export
  r : Double -> CircleOption a f g
  r x = MkCircleOption $ customStrAttr "r" (DynConst $ show x)

  export
  cx : Double -> CircleOption a f g
  cx x = MkCircleOption $ customStrAttr "cx" (DynConst $ show x)

  export
  cxF : (a->Double) -> CircleOption a b
  cxF f = MkCircleOption $ customStrAttr "cx" (DynA $ \(_**x)=> show $ f x)

  export
  cy : Double -> CircleOption a f g
  cy x = MkCircleOption $ customStrAttr "cy" (DynConst $ show x)

  export
  cyF : (a->Double) -> CircleOption a b
  cyF f = MkCircleOption $ customStrAttr "cy" (DynA $ \(_**x)=> show $ f x)

namespace Rect
  export
  rect : List (RectOption a f g) -> SVGElem a f g
  rect = Rect

  export
  x : Double -> RectOption a f g
  x p = MkRectOption $ customStrAttr "x" (DynConst $ show p)

  export
  xF : (a->Double) -> RectOption a b
  xF f = MkRectOption $ customStrAttr "x" (DynA $ \(_**x)=> show $ f x)

  export
  y : Double -> RectOption a f g
  y p = MkRectOption $ customStrAttr "y" (DynConst $ show p)

  export
  yF : (a->Double) -> RectOption a b
  yF f = MkRectOption $ customStrAttr "y" (DynA $ \(_**x)=> show $ f x)

  export
  width : Double -> RectOption a f g
  width p = MkRectOption $ customStrAttr "width" (DynConst $ show p)

  export
  widthF : (a->Double) -> RectOption a b
  widthF f = MkRectOption $ customStrAttr "width" (DynA $ \(_**x)=> show $ f x)

  export
  height : Double -> RectOption a f g
  height p = MkRectOption $ customStrAttr "height" (DynConst $ show p)

  export
  heightF : (a->Double) -> RectOption a b
  heightF f = MkRectOption $ customStrAttr "height" (DynA $ \(_**x)=> show $ f x)

namespace Image
  export
  image : List (ImageOption a f g) -> String -> SVGElem a f g
  image opts s = Image opts (DynConst s)

  export
  x : Double -> ImageOption a f g
  x p = MkImageOption $ customStrAttr "x" (DynConst $ show  p)

  export
  xF : (a->Double) -> ImageOption a b
  xF f = MkImageOption $ customStrAttr "x" (DynA $ \(_**x)=> show $ f x)

  export
  y : Double -> ImageOption a f g
  y p = MkImageOption $ customStrAttr "y" (DynConst $ show p)

  export
  yF : (a->Double) -> ImageOption a b
  yF f = MkImageOption $ customStrAttr "y" (DynA $ \(_**x)=> show $ f x)

  export
  width : Double -> ImageOption a f g
  width p = MkImageOption $ customStrAttr "width" (DynConst $ show p)

  export
  widthF : (a->Double) -> ImageOption a b
  widthF f = MkImageOption $ customStrAttr "width" (DynA $ \(_**x)=> show $ f x)

  export
  height : Double -> ImageOption a f g
  height p = MkImageOption $ customStrAttr "height" (DynConst $ show p)

  export
  heightF : (a->Double) -> ImageOption a b
  heightF f = MkImageOption $ customStrAttr "height" (DynA $ \(_**x)=> show $ f x)

namespace Text
  export
  text : List (TextOption a f g) -> String -> SVGElem a f g
  text opts t = Text opts (DynConst t)

  export
  textF : {t:Type} -> List (TextOption t (const a) (const b)) -> (a->String) -> SVGElem t (const a) (const b)
  textF opts t = Text opts (DynA $ \(_**x) => t x)

  export
  x : Double -> TextOption a f g
  x p = MkTextOption $ customStrAttr "x" (DynConst $ show p)

  export
  xF : (a->Double) -> TextOption a b
  xF f = MkTextOption $ customStrAttr "x" (DynA $ \(_**x)=> show $ f x)

  export
  y : Double -> TextOption a f g
  y p = MkTextOption $ customStrAttr "y" (DynConst $ show p)

  export
  yF : (a->Double) -> TextOption a b
  yF f = MkTextOption $ customStrAttr "y" (DynA $ \(_**x)=> show $ f x)


export
fill : ShapeOption o => String -> o a f g
fill {a} {f} {g} p = shapeAttribute a f g $ CSSAttribute "fill" (DynConst p)

export
transformSVG : ShapeOption o => Transform -> o a f g
transformSVG {a} {f} {g} t = shapeAttribute a f g $ transform t

export
transformSVGF : ShapeOption o => (b -> Transform) -> o a (const b) (const c)
transformSVGF {a} {b} {c} t = shapeAttribute a (const b) (const c) $ transformF t

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
              SVGElem a h g -> SVGElem a f g
  gD = G

  export
  g : {t:Type} -> List (GOption t (const b) (const c)) ->
        (b -> List d) ->
              SVGElem t (const d) (const c) -> SVGElem t (const b) (const c)
  g o f e = G o (\_,z=>f z) e


  export
  onclick : {t:Type} -> (b -> c) -> GOption t (const b) (const c)
  onclick fn = MkGOption $ EventClick $ \_=>fn

export
sG :  List (GOption a f g) -> List (SVGElem a f g) -> SVGElem a f g
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
svgToTempl : SVGElem a f g -> Template a f g
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
svg : List (Attribute a f g) -> List (SVGElem a f g) -> Template a f g
svg attrs childs =
  customNodeNS svgNS "svg" attrs
    (map svgToTempl childs)
