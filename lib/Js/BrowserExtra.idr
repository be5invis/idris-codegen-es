module Js.BrowserExtra

import Js.BrowserTemplate
import public Effects

export
data Html : Effect where
  InitBody : a -> Template a b -> sig Html () () (GuiRef a b)
  Update : (a->a) -> sig Html () (GuiRef a b)
  GetInput : sig Html b (GuiRef a b)

public export
HTML : (ty : Type) -> EFFECT
HTML t = MkEff t Html

export
implementation Handler Html ASync where
  handle () (InitBody x t) k = do  b <- liftJS_IO body; r' <- liftJS_IO $ initTemplate b x t; k () r'
  handle r (Update f) k = do liftJS_IO $ updateTemplate f r; k () r
  handle r GetInput k = do y <- getInputTemplate r; k y r

export
initBody : a -> Template a b -> Eff () [HTML ()] [HTML (GuiRef a b)]
initBody x t = call $ InitBody x t

export
update : (a -> a) -> Eff () [HTML (GuiRef a b)]
update f = call $ Update f

export
getInput : Eff b [HTML (GuiRef a b)]
getInput = call GetInput

export
onchange' : (c -> b) -> InputAttribute a b c
onchange' f = onchange (\_,x=> f x)

export
onclick' : b -> Attribute a b
onclick' x = onclick $ const x

export
span : List (Attribute a b) -> List (Template a b) -> Template a b
span = customNode "span"

export
div : List (Attribute a b) -> List (Template a b) -> Template a b
div = customNode "div"

export
button : IGen c a String => List (Attribute a b) -> c -> Template a b
button attrs x = customNode "button" attrs [text [] x]

export
listOnDivIndex : List (Attribute a b) -> (a -> List c) -> Template (Nat, c) b -> Template a b
listOnDivIndex attrs f t = listOnDiv attrs (\x => let l = f x in zip [0..length l] l) t

maybeConsIdx : Maybe a -> Fin 2
maybeConsIdx Nothing = 0
maybeConsIdx (Just _) = 1

maybeConsIdxType : Type -> Fin 2 -> Type
maybeConsIdxType a FZ = ()
maybeConsIdxType a (FS FZ) = a

export
maybeTemplateSpan : List (Attribute (Maybe a) b) -> Template () b -> Template a b -> Template (Maybe a) b
maybeTemplateSpan {a} {b} attrs tNothing tJust =
  caseTemplateSpan attrs f m2dp templs
  where
    f : Fin 2 -> Type
    f = [(), a]
    m2dp : Maybe a -> DPair (Fin 2) f
    m2dp Nothing = (0 ** ())
    m2dp (Just x) = (1 ** x)
    templs : (x: Fin 2) -> Template (f x) b
    templs FZ = tNothing
    templs (FS FZ) = tJust
