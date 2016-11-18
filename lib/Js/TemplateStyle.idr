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

Show FlexDirection where
  show Row = "row"
  show Column = "column"

public export
data FlexOption = Direction FlexDirection


export
flex : List FlexOption -> Style
flex x =
  CompStyle (MkStyle "display" "flex" :: map stlopt x)
  where
    stlopt : FlexOption -> Style
    stlopt (Direction x) = MkStyle "flex-direction" (show x)
