module TemplateStyle

import Js.BrowserDom

public export
data Style = Width Nat
           | Height Nat


styleStr' : Style -> String
styleStr' (Width x) = "width:" ++ show x ++ ";"
styleStr' (Height x) = "height:" ++ show x ++ ";"

export
styleStr : List Style -> String
styleStr x = foldl (\z,w => z ++ styleStr' w) "" x
