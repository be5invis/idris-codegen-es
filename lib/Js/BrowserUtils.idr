module Js.BrowserUtils

import Js.BrowserBase


public
foldView' : (a -> st -> st) -> st -> View st a -> View st st
foldView' f z v = foldView (\x, s => let ns = f x s in (ns, Just s) ) z v
