module TemplateStyle

import Js.BrowserDom

public export
data Style = Width Nat
           | Height Nat


styleStr : Style -> String
styleStr (Width x) = "width:" ++ show x ++ ";"
styleStr (Height x) = "height:" ++ show x ++ ";"

export
setStyle : List Style -> DomNode -> JS_IO ()
setStyle x n = setAttribute n ("style", foldl (\z,w => z ++ styleStr w) "" x)
