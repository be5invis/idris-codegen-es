module Js.BrowserExtra

import Js.BrowserApp
import public Js.BrowserTemplate

public export
STemplate : Type -> Type -> Type
STemplate x y = Template x (const y)

public export
SimpleApp : Type -> Type -> Type
SimpleApp a b = App a (\_=>b) b

export
mkSimpleApp : AppM b a -> (STemplate a b) -> (a -> b -> AppM b a) -> SimpleApp a b
mkSimpleApp z v u =
  MkApp
    z
    v
    u
    u

export
sonchange : (c -> b) -> InputAttribute  a (const b) c
sonchange h = onchange (\_,z=>h z)
