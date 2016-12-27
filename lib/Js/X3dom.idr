module X3dom

import Js.Browser
import public Data.Matrix.Numeric


export
data Appearance = DiffuseRGB Double Double Double

export
data ShapeOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  AppearanceOption : Appearance -> ShapeOption a f g
  EventClick : ((x:a) -> f x -> g x) -> ShapeOption a f g

public export
Point3 : Type
Point3 = Vect 3 Double

public export
p3 : Double -> Double -> Double -> Point3
p3 x y z = [x,y,z]

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
    (MkTransform (pure [0,0,0]) (pure [1,1,1]))
    x
  where
    reduce (MkTransform t s) (MkTransform t' s') =
      MkTransform
        (zipWith (+) <$> t <*> t')
        (zipWith (*) <$> s <*> s')
  --      ((\[x,y,z],(x',y',z') => (x+x',y+y',z+z')) <$> t <*> t')
  --      ((\(x,y,z),(x',y',z') => (x*x',y*y',z*z')) <$> s <*> s')

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
point3ToString [x,y,z] = show x ++ " " ++ show y ++ " " ++ show z

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


shapeOptToProcs : List (ShapeOption a f g) ->
                  ( DomNode -> GuiCallback a f g -> JS_IO (List (JS_IO ())) , List (JS_IO ()) -> JS_IO ())
shapeOptToProcs x =
  (shapeOptToProcs' x, sequence_)
  where
    shapeClickToProc : ((x:a) -> f x -> g x) ->
                        (DomNode -> GuiCallback a f g -> JS_IO (JS_IO ()))
    shapeClickToProc fn =
      \n,gcb=> do
        i <- genId
        jscall "(function(){if(!window.x3domFnDict){window.x3domFnDict = {}}})()" (()->JS_IO ()) ()
        jscall "window.x3domFnDict[%0] = %1" (Int -> (JsFn (() -> JS_IO ())) -> JS_IO ()) i (MkJsFn $ procClick gcb fn)
        setAttribute n ("onclick", "try{window.x3domFnDict[" ++ show i ++ "] ()}catch(err){console.log(err)}")
        pure (jscall "delete window.x3domFnDict[%0]" (Int -> JS_IO ()) i)
    shapeOptToProcs' :List (ShapeOption a f g) ->
                        ( DomNode -> GuiCallback a f g -> JS_IO (List (JS_IO ())))
    shapeOptToProcs' [] =
      \_,_=> pure []
    shapeOptToProcs' (EventClick fn::r) =
      \x,y => do
        t <- shapeClickToProc fn x y
        r' <- shapeOptToProcs' r x y
        pure (t::r')
    shapeOptToProcs' (_::r) =
      shapeOptToProcs' r

x3domToTempl : BElement a f g -> Template a f g
x3domToTempl (Sphere opt) =
  customNodeWidthPostProc
    (shapeOptToProcs opt)
    "shape"
    []
    (customNode  "sphere" [] [] :: shapeOptToNodes opt )
x3domToTempl (Box opt) =
  customNodeWidthPostProc
    (shapeOptToProcs opt)
    "shape"
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
  customNodeWidthPostProc (\_,_=> jscall "x3dom.reload()" (() -> JS_IO()) (), \_=> pure ()) "x3d" attrs
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
translation x = MkTransform (getDyn x) (pure [1,1,1])

export
scale : IDyn s (DPair a f) Point3 => s -> Transform a f
scale x = MkTransform (pure [0,0,0]) (getDyn x)

export
transform : List (Transform a f) -> List (BElement a f g) -> BElement a f g
transform x y = TransformElem x y


export
rgb : Double -> Double -> Double -> ShapeOption a f g
rgb x y z = AppearanceOption $ DiffuseRGB x y z

export
viewPoint : Point3 -> Point3 -> Double -> SceneOption a f
viewPoint = ViewPoint
