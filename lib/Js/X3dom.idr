module X3dom

import Js.Browser


export
data Appearance = DiffuseRGB Double Double Double

public export
Point3 : Type
Point3 = (Double, Double, Double)

export
interface ToDouble a where
  toDouble : a -> Double

export
ToDouble Integer where
  toDouble = cast

export
ToDouble Double where
  toDouble = id

export
(ToDouble b, ToDouble c, ToDouble d) => IGen (b, c, d) a Point3 where
  getGen (x,y,z) = GenConst (toDouble x, toDouble y, toDouble z)

export
data Transform : (a:Type) -> (a->Type) -> Type where
  MkTransform : (Gen (DPair a f) Point3) -> (Gen (DPair a f) Point3) -> Transform a f

export
data NavigationType = NavigationNone

export
data SceneOption : (a:Type) -> (a->Type) -> Type where
  ViewPoint : Point3 -> Point3 -> Double -> SceneOption a f
  Navigation : NavigationType -> SceneOption a f

foldTransforms : List (Transform a f) -> Transform a f
foldTransforms x =
  foldl
    reduce
    (MkTransform (pure (0,0,0)) (pure (1,1,1)))
    x
  where
    reduce (MkTransform t s) (MkTransform t' s') =
      MkTransform
        ((\(x,y,z),(x',y',z') => (x+x',y+y',z+z')) <$> t <*> t')
        ((\(x,y,z),(x',y',z') => (x*x',y*y',z*z')) <$> s <*> s')

export
data Element : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  Sphere : Appearance -> Element a f g
  Box : Appearance -> Element a f g
  TransformElem : List (Transform a f) -> List (Element a f g) -> Element a f g

appearanceToTemplate : Appearance -> Template a f g
appearanceToTemplate (DiffuseRGB r g b) =
  customNode "appearance"
    []
    [customNode "material" [StrAttribute "diffuseColor" (pure $ show r ++ " " ++ show g ++ " " ++ show b) ] []]

integerToString : Integer -> String
integerToString = show

point3ToString : Point3 -> String
point3ToString (x,y,z) = show x ++ " " ++ show y ++ " " ++ show z

width : IGen w (DPair a f) Integer => w -> Attribute a f g
width x = StrAttribute "width" (map integerToString $ getGen x)

height : IGen h (DPair a f) Integer => h -> Attribute a f g
height h = StrAttribute "height" (map integerToString $ getGen h)

transformToAttr : Transform a f -> List (Attribute a f g)
transformToAttr (MkTransform t s) =
  [ StrAttribute "translation" (point3ToString <$> t)
  , StrAttribute "scale" (point3ToString <$> s)
  ]

x3domToTempl : Element a f g -> Template a f g
x3domToTempl (Sphere ap) =
  customNode "shape"
    []
    [appearanceToTemplate ap, customNode "sphere" [] []]
x3domToTempl (Box ap) =
  customNode "shape"
    []
    [appearanceToTemplate ap, customNode "box" [] []]
x3domToTempl (TransformElem transfs chlds) =
  customNode "transform"
    (transformToAttr $ foldTransforms transfs)
    (map x3domToTempl chlds)

makeSceneOption : SceneOption a f -> Template a f g
makeSceneOption (ViewPoint pos vect angl) =
  customNode "ViewPoint"
    [ StrAttribute "position" (pure $ point3ToString pos)
    , StrAttribute "orientation" (pure $ point3ToString vect ++ " " ++ show angl)
    ]
    []
makeSceneOption (Navigation NavigationNone) =
  customNode "navigationInfo"
    [StrAttribute "type" (pure "none")]
    []

export
x3dom : List (Attribute a f g) -> List (SceneOption a f) -> List (Element a f g) -> Template a f g
x3dom attrs options childs =
  customNodeWidthPostProc (\_=> jscall "x3dom.reload()" (() -> JS_IO()) ()) "x3d" attrs
    [customNode "scene" []
       (map makeSceneOption options ++ map x3domToTempl childs)
    ]

--------------------------------------------------------------------------------

export
sphere : Appearance -> Element a f g
sphere = Sphere

export
box : Appearance -> Element a f g
box = Box

export
translation : IGen t (DPair a f) Point3 => t -> Transform a f
translation x = MkTransform (getGen x) (pure (1,1,1))

export
scale : IGen s (DPair a f) Point3 => s -> Transform a f
scale x = MkTransform (pure (0,0,0)) (getGen x)

export
transform : List (Transform a f) -> List (Element a f g) -> Element a f g
transform x y = TransformElem x y


export
rgb : Double -> Double -> Double -> Appearance
rgb = DiffuseRGB

export
viewPoint : Point3 -> Point3 -> Double -> SceneOption a f
viewPoint = ViewPoint
