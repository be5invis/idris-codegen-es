module SVG

import Js.Browser

export
data SVG : Type -> Type -> Type where
  ImageSvg : Gen a Int -> Gen a Int -> Gen a Nat -> Gen a Nat -> Gen a String -> SVG a b

posx : Gen a Int -> Attribute a f
posx x = StrAttribute "x" (map show x)

posy : Gen a Int -> Attribute a f
posy y = StrAttribute "y" (map show y)

width : Gen a Nat -> Attribute a f
width w = StrAttribute "width" (map show w)

height : Gen a Nat -> Attribute a f
height h = StrAttribute "height" (map show h)

svg2templ : SVG a f -> Template a f
svg2templ (ImageSvg x y w h i) = customNode "image" [posx x, posy y, width w, height h, StrAttribute "xlink:href" i] []

export
svg : Gen a Nat -> Gen a Nat -> List (SVG a f) -> Template a f
svg w h l = customNode "svg" [width w, height h] (map svg2templ l)


export
image : Gen a Int -> Gen a Int -> Gen a Nat -> Gen a Nat -> Gen a String -> SVG a f
image = ImageSvg
