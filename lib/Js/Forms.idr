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
data Form : (a:Type) -> (a->Type) -> Type where
  MkForm : ((x:a) -> MError (g x)) ->
              ((x:a) -> (y:a) -> MError (g x) -> MError (g y)) ->
                List (Template a (Maybe . MError . g) (MError . g)) ->
                  Form a g

MkFormS : {t:Type} -> MError b -> List (Template t (const (Maybe (MError b))) (const (MError b))) -> Form t (const b)
MkFormS i t = MkForm (\_=>i) (\_,_,x=>x) t

FoldState : (a:Type) -> (a->Type)-> a -> Type
FoldState a g x = (MError (g x), Maybe (MError (g x)))


toFoldAttrs : List (InputAttribute a f g c) -> List (FoldAttribute a f g (FoldState a c) c)
toFoldAttrs Nil = Nil
toFoldAttrs ((GenAttr _)::r) = toFoldAttrs r
toFoldAttrs ((OnChange f)::r) = (OnEvent f)::toFoldAttrs r
toFoldAttrs ((SetVal f)::r) = SetState (\z,w=> (\k=>(Right k, Just (Right k))) <$> f z w) :: toFoldAttrs r

export
bform : List (InputAttribute a f g c) -> Form a c -> Template a f g
bform {a} {f} {g} {c} attrs (MkForm v0 conv tmpls) =
  foldTemplate
    (\z=>(v0 z,Nothing))
    upd
    updParam
    (Js.HtmlUtils.Dependent.form
      (\_,_=>Submit)
      []
      formContent
    )
    (toFoldAttrs attrs)
  where
    convTempl : Template a (Maybe . MError . c) (MError . c) -> Template a (FoldState a c) (FormEvent . MError . c)
    convTempl t = (\_,w=> snd w) >$< ((\_,w=>Value w) <$> t)

    formContent : List (Template a (FoldState a c) (FormEvent . MError . c))
    formContent = text [] (dynD $ \(x**(z,_))=>errstr z) :: (map convTempl tmpls)

    updParam : (x:a) -> (y:a) -> FoldState a c x -> FoldState a c y
    updParam x y (z,w) = (conv x y z, conv x y <$> w)

    upd : (x:a) -> FoldState a c x -> FormEvent (MError (c x)) -> (FoldState a c x, Maybe (c x))
    upd x _ (Value k) = ((k,Nothing), Nothing)
    upd x (Right k, _) Submit = let i = v0 x in ((i, Just i), Just k)
    upd x (Left err,_) Submit = ((Left err,Nothing),Nothing)


------ Forms ---------

export
textform : Form a (const String)
textform =
  MkFormS (Left []) [inpBox]
  where
    setV : Maybe (MError String) -> Maybe String
    setV (Just (Right s)) = Just s
    setV _ = Nothing

    inpBox : Template (Maybe (MError String)) (MError String)
    inpBox = textinput [onchange' (\s=>Right s), setVal setV]
