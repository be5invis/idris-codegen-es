module X3dom

import Js.Browser


export
data Appearance = DiffuseRGB Double Double Double

export
data ShapeOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  AppearanceOption : Appearance -> ShapeOption a f g
  EventClick : ((x:a) -> f x -> g x) -> ShapeOption a f g

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
(ToDouble b, ToDouble c, ToDouble d) => IDyn (b, c, d) a Point3 where
  getDyn (x,y,z) = DynConst (toDouble x, toDouble y, toDouble z)

export
data Transform : (a:Type) -> (a->Type) -> Type where
  MkTransform : (Dyn (DPair a f) Point3) -> (Dyn (DPair a f) Point3) -> Transform a f

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
data BElement : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  Sphere : List (ShapeOption a f g) -> BElement a f g
  Box : List (ShapeOption a f g) -> BElement a f g
  TransformElem : List (Transform a f) -> List (BElement a f g) -> BElement a f g
  Group : ((x:a) -> f x -> List (h x)) ->
              BElement a h g -> BElement a f g

appearanceToTemplate : Appearance -> Template a f g
appearanceToTemplate (DiffuseRGB r g b) =
  customNode "appearance"
    []
    [customNode "material" [StrAttribute "diffuseColor" (pure $ show r ++ " " ++ show g ++ " " ++ show b) ] []]

integerToString : Integer -> String
integerToString = show

point3ToString : Point3 -> String
point3ToString (x,y,z) = show x ++ " " ++ show y ++ " " ++ show z

width : IDyn w (DPair a f) Integer => w -> Attribute a f g
width x = StrAttribute "width" (map integerToString $ getDyn x)

height : IDyn h (DPair a f) Integer => h -> Attribute a f g
height h = StrAttribute "height" (map integerToString $ getDyn h)

transformToAttr : Transform a f -> List (Attribute a f g)
transformToAttr (MkTransform t s) =
  [ StrAttribute "translation" (point3ToString <$> t)
  , StrAttribute "scale" (point3ToString <$> s)
  ]

shapeOptToNodes : List (ShapeOption a f g) -> List (Template a f g)
shapeOptToNodes [] = []
shapeOptToNodes ((AppearanceOption x)::r) = appearanceToTemplate x :: shapeOptToNodes r
shapeOptToNodes (_::r) = shapeOptToNodes r

shapeOptToAttrs : List (ShapeOption a f g) -> List (Attribute a f g)
shapeOptToAttrs [] = []
shapeOptToAttrs ((EventClick f)::r) = EventClick f :: shapeOptToAttrs r
shapeOptToAttrs (_::r) = shapeOptToAttrs r

x3domToTempl : BElement a f g -> Template a f g
x3domToTempl (Sphere opt) =
  customNode "shape"
    (shapeOptToAttrs opt)
    (customNode  "sphere" [] [] :: shapeOptToNodes opt )
x3domToTempl (Box opt) =
  customNode "shape"
    []
    (customNode  "box" [] [] :: shapeOptToNodes opt )
x3domToTempl (TransformElem transfs chlds) =
  customNode "transform"
    (transformToAttr $ foldTransforms transfs)
    (map x3domToTempl chlds)
x3domToTempl (Group fn elem) =
  listCustom "Group" [] fn (x3domToTempl elem)

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
x3dom : List (Attribute a f g) -> List (SceneOption a f) -> List (BElement a f g) -> Template a f g
x3dom attrs options childs =
  customNodeWidthPostProc (\_=> jscall "x3dom.reload()" (() -> JS_IO()) ()) "x3d" attrs
    [customNode "scene" []
       (map makeSceneOption options ++ map x3domToTempl childs)
    ]

--------------------------------------------------------------------------------


namespace Dependent
  public export
  Element : (a:Type) -> (a->Type) -> (a->Type) -> Type
  Element = BElement

  export
  group : ((x:a) -> f x -> List (h x)) ->
              BElement a h g -> BElement a f g
  group fn = Group fn

  export
  groupIndex : {h:a->Type} -> ((x:a) -> f x -> List (h x)) ->
                          BElement a (\x=> (Nat, h x)) g -> BElement a f g
  groupIndex fn t = group (\x,y => let l = fn x y in zip [0..length l] l) t

namespace Simple
  public export
  Element : {t:Type} -> Type -> Type -> Type
  Element {t} b c = BElement t (const b) (const c)

  export
  group : {t:Type} -> (b -> List d) ->
              BElement t (const d) (const c) -> BElement t (const b) (const c)
  group fn = Group (\_,y=> fn y)


  export
  groupIndex : {t:Type} -> (b -> List d) ->
              BElement t (const (Nat,d)) (const c) -> BElement t (const b) (const c)
  groupIndex {d} fn = X3dom.Dependent.groupIndex {h=\_=>d} (\_,y=> fn y)

  export
  onclick : {t:Type} -> (b -> c) -> ShapeOption t (const b) (const c)
  onclick fn = EventClick (\_,y=>fn y)

  export
  onclick' : {t:Type} -> c -> ShapeOption t (const b) (const c)
  onclick' x = onclick (const x)

export
sphere : List (ShapeOption a f g) -> BElement a f g
sphere = Sphere

export
box : List (ShapeOption a f g) -> BElement a f g
box = Box

export
translation : IDyn t (DPair a f) Point3 => t -> Transform a f
translation x = MkTransform (getDyn x) (pure (1,1,1))

export
scale : IDyn s (DPair a f) Point3 => s -> Transform a f
scale x = MkTransform (pure (0,0,0)) (getDyn x)

export
transform : List (Transform a f) -> List (BElement a f g) -> BElement a f g
transform x y = TransformElem x y


export
rgb : Double -> Double -> Double -> ShapeOption a f g
rgb x y z = AppearanceOption $ DiffuseRGB x y z

export
viewPoint : Point3 -> Point3 -> Double -> SceneOption a f
viewPoint = ViewPoint
