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
data Transform a = MkTransform (Gen a Point3) (Gen a Point3)

export
data NavigationType = NavigationNone

export
data SceneOption a = ViewPoint Point3 Point3 Double
                   | Navigation NavigationType

foldTransforms : List (Transform a) -> Transform a
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
data Element : (a:Type) -> (a->Type) -> Type where
  Sphere : Appearance -> Element a f
  Box : Appearance -> Element a f
  TransformElem : List (Transform a) -> List (Element a f) -> Element a f

appearanceToTemplate : Appearance -> Template a f
appearanceToTemplate (DiffuseRGB r g b) =
  customNode "appearance"
    []
    [customNode "material" [StrAttribute "diffuseColor" (pure $ show r ++ " " ++ show g ++ " " ++ show b) ] []]

integerToString : Integer -> String
integerToString = show

point3ToString : Point3 -> String
point3ToString (x,y,z) = show x ++ " " ++ show y ++ " " ++ show z

width : IGen w a Integer => w -> Attribute a f
width x = StrAttribute "width" (map integerToString $ getGen x)

height : IGen h a Integer => h -> Attribute a f
height h = StrAttribute "height" (map integerToString $ getGen h)

transformToAttr : Transform a -> List (Attribute a f)
transformToAttr (MkTransform t s) =
  [ StrAttribute "translation" (point3ToString <$> t)
  , StrAttribute "scale" (point3ToString <$> s)
  ]

x3domToTempl : Element a f -> Template a f
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

makeSceneOption : SceneOption a -> Template a f
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
x3dom : List (Attribute a f) -> List (SceneOption a) -> List (Element a f) -> Template a f
x3dom attrs options childs =
  customNode "x3d" attrs
    [customNode "scene" []
       (map makeSceneOption options ++ map x3domToTempl childs)
    ]

--------------------------------------------------------------------------------

export
sphere : Appearance -> Element a f
sphere = Sphere

export
box : Appearance -> Element a f
box = Box

export
translation : IGen t a Point3 => t -> Transform a
translation x = MkTransform (getGen x) (pure (1,1,1))

export
scale : IGen s a Point3 => s -> Transform a
scale x = MkTransform (pure (0,0,0)) (getGen x)

export
transform : List (Transform a) -> List (Element a f) -> Element a f
transform x y = TransformElem x y


export
rgb : Double -> Double -> Double -> Appearance
rgb = DiffuseRGB

export
viewPoint : Point3 -> Point3 -> Double -> SceneOption a
viewPoint = ViewPoint
