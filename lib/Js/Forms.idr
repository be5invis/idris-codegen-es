module Js.Forms

import Js.Browser

public export
TyError : Type
TyError = List String

public export
MError : Type -> Type
MError a = Either TyError a

errors : MError a -> List String
errors (Right _) = []
errors (Left x)  = x

errstr : MError a -> String
errstr x = foldl (\x,y=>x++";"++y) "" $ errors x

public export
data FormEvent a = Value a | Submit


public export
data Form : (a:Type) -> Type where
  MkForm : (MError a) -> ({b:Type} -> {c:Type} -> (MError a -> b) -> (c -> Maybe (MError a)) -> List (Template c b)) -> Form a




toFoldAttrs : List (InputAttribute a f b) -> List (FoldAttribute a f (MError b, Maybe (MError b)) b)
toFoldAttrs Nil = Nil
toFoldAttrs ((GenAttr _)::r) = toFoldAttrs r
toFoldAttrs ((OnChange f)::r) = (OnEvent f)::toFoldAttrs r
toFoldAttrs ((DynSetVal f)::r) = (DynSetState (\x=> ((\z=>(z, Just z)) . Right) <$> f x ))::toFoldAttrs r

export
bform : List (InputAttribute a f b) -> Form b -> Template a f
bform {b} attrs (MkForm init tmpl) =
  foldTemplate
    (init, Nothing)
    upd
    (form
      (the ((MError b, Maybe (MError b)) -> FormEvent (MError b)) $ const Submit)
      []
      (dyntext [] (errstr . fst) :: tmpl Value snd)
    )
    (toFoldAttrs attrs)
  where
    upd : (MError b, Maybe (MError b)) -> FormEvent (MError b) -> ((MError b, Maybe (MError b)), Maybe b)
    upd _ (Value x) = ((x, Nothing), Nothing)
    upd (Right x,_) Submit = ((init,Just init), Just x)
    upd (Left err,_) Submit = ((Left err,Nothing), Nothing)

------ Forms ---------

export
textform : Form String
textform =
  MkForm (Left []) (\proce, procs => [textinput [onchange' (sch proce), dynsetval (sval procs)]])
  where
    sval : (c -> Maybe (MError String)) -> c -> Maybe String
    sval p x =
      case p x of
        Nothing => Nothing
        Just (Left _) => Just ""
        Just (Right x) => Just x
    sch : (MError String -> b) -> String -> b
    sch h x = h (Right x)
