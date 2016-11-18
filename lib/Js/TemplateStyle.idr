module TemplateStyle

import Js.BrowserDom

public export
data Style = MkStyle String String
           | CompStyle (List Style)

mutual
  styleStr' : Style -> String
  styleStr' (MkStyle k x) = k ++ ":" ++ x ++ ";"
  styleStr' (CompStyle x) = styleStr x

  export
  styleStr : List Style -> String
  styleStr x = foldl (\z,w => z ++ styleStr' w) "" x

export
height : Nat -> Style
height x = MkStyle "height" (show x)

export
width : Nat -> Style
width x = MkStyle "width" (show x)

public export
data FlexDirection = Row | Column

public export
data FlexOptions = Direction FlexDirection


export
flex : List FlexOptions -> Style
flex x =
  CompStyle (MkStyle "display" "flex" :: map stlopt x)
  where
    stlopt (FlexDirection Row) = MkStyle "flex-direction" "row"
    stlopt (FlexDirection Column) = MkStyle "flex-direction" "column"
