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


--listTemplate : Eq b => (a -> List b) -> Template (a,b) (f . Prelude.Basics.fst) -> Template a f

--export
--slistTemplate : Eq b => (a -> List b) -> Template

{-
export
sfoldTemplate : b -> (STemplate b e) ->
                (b -> e -> (b, Maybe r)) ->
                  STemplate a r
sfoldTemplate x y z = foldTemplate x y (\_,w,k=>z w k)
-}
