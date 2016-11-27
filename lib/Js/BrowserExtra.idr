module Js.BrowserExtra

import Js.BrowserTemplate
import public Effects

%access export

data Html : Effect where
  InitBody : a -> Template a b -> sig Html () () (TemplateRef a b)
  Update : (a->a) -> sig Html () (TemplateRef a b) (TemplateRef a b)
  GetInput : sig Html b (TemplateRef a b) (TemplateRef a b)

export
HTML : (ty1 : Type) -> (ty2 : Type) -> EFFECT
HTML t1 t2 = MkEff (t1, t2) Html

export
implementation Handler Html ASync where
  handle r (InitBody x t) k = do  b <- liftJS_IO body; r' <- liftJS_IO $ initTemplate b x t; k () r'
  handle r (Update f) k = do liftJS_IO $ updateTemplate f r; k () r
  handle r GetInput k = do y <- getInputTemplate r; k y r

onchange' : (c -> b) -> InputAttribute  a b c
onchange' f = onchange (\_,x=> f x)

export
span : List (Attribute a f) -> List (Template a f) -> Template a f
span = customNode "span"

export
div : List (Attribute a f) -> List (Template a f) -> Template a f
div = customNode "div"


listOnDivIndex : List (Attribute a b) -> (a -> List c) -> Template (Nat, c) b -> Template a b
listOnDivIndex attrs f t = listOnDiv attrs (\x => let l = f x in zip [0..length l] l) t

private
maybeConsIdx : Maybe a -> Fin 2
maybeConsIdx Nothing = 0
maybeConsIdx (Just _) = 1

private
maybeConsIdxType : Type -> Fin 2 -> Type
maybeConsIdxType a FZ = ()
maybeConsIdxType a (FS FZ) = a


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
