module BrowserTemplate

import Js.BrowserDom
import public Data.Vect
import Js.ASync


public export
data Style = MkStyle String String
           | CompStyle (List Style)

mutual
  styleStr' : Style -> String
  styleStr' (MkStyle k x) = k ++ ":" ++ x ++ ";"
  styleStr' (CompStyle x) = styleStr x

  styleStr : List Style -> String
  styleStr x = foldl (\z,w => z ++ styleStr' w) "" x


public export
data Gen a b = GenConst b | GenA (a->b)

public export
interface IGen c a b where
  getGen : c -> Gen a b

export
IGen b a b where
  getGen x = GenConst x

export
IGen (a -> b) a b where
  getGen x = GenA x

export
Functor (Gen a) where
  map f (GenConst x) = GenConst (f x)
  map f (GenA x) = GenA (f . x)

export
Applicative (Gen a) where
  pure = GenConst

  (<*>) (GenConst f) fa = f <$> fa
  (<*>) (GenA f) (GenA fa) = GenA (\x => (f x) (fa x))
  (<*>) (GenA f) (GenConst fa) = GenA (\x => (f x) fa)



data InputType = IText

inputTypeTy : InputType -> Type
inputTypeTy IText = String


public export
data Attribute : (a:Type) -> (a->Type) -> Type where
  EventClick : ((x:a) -> f x) -> Attribute a f
  StrAttribute : String -> Gen a String -> Attribute a f

public export
data InputAttribute : (a:Type) -> (a->Type) -> Type -> Type where
  GenAttr : Attribute a f -> InputAttribute a f y
  OnChange : ((x:a) -> y -> f x) -> InputAttribute a f y
  DynSetVal : (a -> Maybe y) -> InputAttribute a f y


public export
data FoldAttribute : (a:Type) -> (a -> Type) -> Type -> Type -> Type where
  OnEvent : ((x:a) -> r -> f x) -> FoldAttribute a f b r
  DynSetState : (a -> Maybe b) -> FoldAttribute a f b r


export
data Template : (a:Type) -> (a->Type) -> Type where
  CustomNode : String -> List (Attribute a f) -> List (Template a f) -> Template a f
  TextNode : List (Attribute a f) -> String -> Template a f
  DynTextNode : List (Attribute a f) ->
                  (a -> String) -> Template a f
  InputNode : (t:InputType) -> List (InputAttribute a f (inputTypeTy t)) ->
                  Template a f
  FoldNode : b -> (b->i->(b,Maybe r)) -> Template b (const i) -> List (FoldAttribute a f b r) -> Template a f
  FormNode : ((x:a) -> f x) -> List (Attribute a f) -> List (Template a f) -> Template a f
  ListTemplateNode : String -> List (Attribute a f) -> (a -> List b) ->
                          Template (a,b) (f . Prelude.Basics.fst) -> Template a f
  ImgNode : List (Attribute a f) -> String -> Template a f

data Update : Type -> Type where
  MkUpdate : (a -> b) -> (b -> b -> JS_IO ()) -> Update a

Remove : Type
Remove = JS_IO ()

Updates : Type -> Type
Updates a = List (Update a)


procChange : {f:a->Type} -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) ->
                  (String -> y) -> ((x:a) -> y -> f x) -> String -> JS_IO ()
procChange get pr j h str =
  do
    x <- get
    pr x (h x (j str))

procClick : {f:a->Type} -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> ((x:a) -> f x) -> () -> JS_IO ()
procClick get pr h () =
  do
    x <- get
    pr x (h x)

updateStrAttribute : DomNode -> String -> String -> String -> JS_IO ()
updateStrAttribute n name x1 x2 =
  if x1 == x2 then pure ()
    else setAttribute n (name, x2)

initAttribute : a -> DomNode -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> Attribute a f -> JS_IO (Maybe (Update a))
initAttribute _ n getst proc (EventClick h) =
  do
    registEvent (procClick getst proc h) n "click" (pure ())
    pure Nothing
initAttribute _ n getst proc (StrAttribute name (GenConst x) ) =
  do
    setAttribute n (name, x)
    pure Nothing
initAttribute v n getst proc (StrAttribute name (GenA x) ) =
  do
    setAttribute n (name, x v)
    pure $ Just $ MkUpdate x (updateStrAttribute n name)

initAttributes : a -> DomNode -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> List (Attribute a f) -> JS_IO (List (Update a))
initAttributes v n getst proc attrs = (catMaybes<$>) $ sequence $ map (initAttribute v n getst proc) attrs

procSetVal : DomNode -> Maybe String -> JS_IO ()
procSetVal _ Nothing = pure ()
procSetVal n (Just z) =
  setValue z n

initAttributeInp : a -> DomNode -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) ->
                      (String -> y) -> (y -> String) -> InputAttribute a f y -> JS_IO (Maybe (Update a))
initAttributeInp v n getst proc _ _ (GenAttr x) =
    initAttribute v n getst proc x
initAttributeInp _ n getst proc f _ (OnChange h) =
  do
    registEvent (procChange getst proc f h) n "change" targetValue
    pure Nothing
initAttributeInp v n getst proc _ f (DynSetVal h) =
  do
    procSetVal n (f <$> h v)
    pure $ Just $ MkUpdate ((f<$>) . h) (\_,y=> procSetVal n y)

initAttributesInp : a -> DomNode -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) ->
                      (String -> y) -> (y -> String) -> List (InputAttribute a f y) -> JS_IO (List (Update a))
initAttributesInp v n getst proc f j attrs =
  (catMaybes<$>) $ sequence $ map (initAttributeInp v n getst proc f j) attrs

export
data TemplateState : Type -> Type where
  MkTemplateState : DomNode -> (x:a) -> Updates a -> TemplateState a

procUpdate : a -> a -> Update a -> JS_IO ()
procUpdate old new (MkUpdate r u) =
  u (r old) (r new)

procUpdates : a -> a -> Updates a -> JS_IO ()
procUpdates oz z upds = sequence_ $ map (procUpdate oz z) upds


setState : Ctx (Updates b) -> Ctx b -> Maybe b -> Maybe b -> JS_IO ()
setState _ _ _ Nothing = pure ()
setState ctxU ctxS _ (Just z) =
  do
    oz <- getCtx ctxS
    setCtx ctxS z
    upds <- getCtx ctxU
    procUpdates oz z upds

procOnEvent : JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> r ->
                  List (FoldAttribute a f b r) -> JS_IO ()
procOnEvent _ _ _ [] =
  pure ()
procOnEvent geta proc z ((OnEvent h)::r) =
  do
    x <- geta
    proc x (h x z)
procOnEvent geta proc z ((DynSetState h)::r) =
  procOnEvent geta proc z r

calcFoldUpdatesList: Ctx (Updates b) -> Ctx b -> List (FoldAttribute a f b r) -> Updates a
calcFoldUpdatesList _ _ Nil = []
calcFoldUpdatesList x y ((OnEvent _)::r) = calcFoldUpdatesList x y r
calcFoldUpdatesList x y ((DynSetState h)::_) =
  [MkUpdate h (setState x y)]


updateFold : Ctx (Updates b) -> Ctx b -> (b->i->(b,Maybe r)) ->
              JS_IO a -> List (FoldAttribute a f b r) -> ((x:a) -> f x -> JS_IO ()) ->
                b -> i -> JS_IO ()
updateFold ctxU ctxS updfn geta attrs proc st e =
  do
    let (newst, mr) = updfn st e
    setCtx ctxS newst
    upds <- getCtx ctxU
    procUpdates st newst upds
    case mr of
      Nothing => pure ()
      Just x => procOnEvent geta proc x attrs

removeListNodes : List (Remove, Updates a) -> JS_IO ()
removeListNodes x =
  sequence_ $ map fst x

mutual

  updateListTemplate : Nat -> DomNode -> a -> a -> JS_IO a ->
                            ((x:a) -> f x -> JS_IO ()) -> (a -> List b) ->
                              Template (a,b) (f . Prelude.Basics.fst) ->
                                List b -> List b -> List (Remove, Updates (a,b)) -> JS_IO (List (Remove, Updates (a, b)))
  updateListTemplate pos nd v v' getst proc h t (x::xs) (y::ys) ((r,u)::us) =
    do
      procUpdates (v,x) (v',y) u
      us' <- updateListTemplate (S pos) nd v v' getst proc h t xs ys us
      pure $ (r,u)::us'
  updateListTemplate pos nd v v' getst proc h t [] ys [] =
    addListTemplateNodes pos nd v' getst proc h t ys
  updateListTemplate pos nd v v' getst proc h t xs [] us =
    do
      removeListNodes us
      pure []


  updateLT : DomNode -> JS_IO a ->
              ((x:a) -> f x -> JS_IO ()) -> (a -> List b) ->
                  Template (a,b) (f . Prelude.Basics.fst) -> Ctx (List (Remove,Updates (a,b))) ->
                    a -> a -> JS_IO ()
  updateLT nd getst proc h t ctx o n =
    do
      upds <- getCtx ctx
      upds' <- updateListTemplate 0 nd o n getst proc h t (h o) (h n) upds
      setCtx ctx upds'

  addListTemplateNodes : Nat -> DomNode -> a -> JS_IO a ->
                            ((x:a) -> f x -> JS_IO ()) -> (a -> List b) ->
                              Template (a,b) (f . Prelude.Basics.fst) -> List b -> JS_IO (List (Remove, Updates (a, b)))
  addListTemplateNodes {a} {b} pos nd v getst proc h t [] = pure []
  addListTemplateNodes {a} {b} pos nd v getst proc h t (x::xs) =
    do
      us <- initTemplate' nd (v, x) (getstAux <$> getst) (\(z,_),w=>proc z w) t
      us' <- addListTemplateNodes (S pos) nd v getst proc h t xs
      pure $ us :: us'
    where
      getstAux : a -> (a,b)
      getstAux x =
        case index' pos $ h x of
          Just y => (x, y)

  initChilds : DomNode -> a -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> List (Template a f) -> JS_IO (Remove, Updates a)
  initChilds n v getst proc childs =
    do
      w <- (sequence $ map (initTemplate' n v getst proc) childs)
      pure (sequence_ $ map fst w, concat $ map snd w)

  initTemplate' : DomNode -> a -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> Template a f -> JS_IO (Remove, Updates a)
  initTemplate' n v getst proc (CustomNode tag attrs childs) =
    do
      newn <- appendNode n tag
      attrsUpds <- initAttributes v newn getst proc attrs
      (cr, childsUpds) <- initChilds newn v getst proc childs
      pure (cr >>= \_ => removeDomNode newn, attrsUpds ++ childsUpds)
  initTemplate' n v getst proc (TextNode attrs str) =
    do
      newn <- appendNode n "span"
      setText str newn
      attrUpds <- initAttributes v newn getst proc attrs
      pure (removeDomNode newn, attrUpds)
  initTemplate' n v getst proc (DynTextNode attrs getter) =
    do
      newn <- appendNode n "span"
      setText (getter v) newn
      attrsUpds <- initAttributes v newn getst proc attrs
      pure (removeDomNode newn, MkUpdate getter (\x,y => if x ==y then pure () else setText y newn) :: attrsUpds)
  initTemplate' n v getst proc (InputNode IText attrs) =
    do
      i <- appendNode n "input"
      setAttribute i ("type", "text")
      attrsUpds <- initAttributesInp v i getst proc id id attrs
      pure (removeDomNode i, attrsUpds)
  initTemplate' n v getst proc (FoldNode {a} {f} {b} {i} {r} s0 fupd t attrs) =
    do
      ctxS <- makeCtx s0
      ctxU <- makeCtx []
      (r, upds) <- initTemplate'
                n
                s0
                (getCtx ctxS)
                (updateFold {a=a} {f=f} {b=b} {i=i} ctxU ctxS fupd getst attrs proc)
                t
      setCtx ctxU upds
      pure (r, calcFoldUpdatesList ctxU ctxS attrs)
  initTemplate' n v getst proc (FormNode submit attrs childs) =
    do
      frm <- appendNode n "form"
      registEvent (procClick getst proc submit) frm "submit" preventDefault
      attrsUpds <- initAttributes v frm getst proc attrs
      (cr, childsUpds) <- initChilds frm v getst proc childs
      pure (cr >>= \_ => removeDomNode frm, attrsUpds ++ childsUpds)
  initTemplate' n v getst proc (ListTemplateNode tag attrs h t) =
    do
      newn <- appendNode n tag
      attrsUpds <- initAttributes v newn getst proc attrs
      upds <- addListTemplateNodes 0 newn v getst proc h t (h v)
      ctxU <- makeCtx upds
      pure (getCtx ctxU >>= removeListNodes >>= \_ => removeDomNode newn
           , (MkUpdate id (updateLT newn getst proc h t ctxU)) :: attrsUpds)
  initTemplate' n v getst proc (ImgNode attrs x) =
    do
      nd <- appendNode n "img"
      setAttribute nd ("src", x)
      attrsUpds <- initAttributes v nd getst proc attrs
      pure (removeDomNode nd, attrsUpds)



export
initTemplate : DomNode -> a -> JS_IO a -> ((x:a) -> f x -> JS_IO ()) -> Template a f -> JS_IO (TemplateState a)
initTemplate n v getst proc t = pure $ MkTemplateState n v (snd !(initTemplate' n v getst proc t))

export
updateTemplate : a -> TemplateState a-> JS_IO (TemplateState a)
updateTemplate x (MkTemplateState n oldx upds) =
  do
    procUpdates oldx x upds
    pure (MkTemplateState n x upds)


---------- Primitives -------------
export
span : List (Attribute a f) -> List (Template a f) -> Template a f
span = CustomNode "span"

export
div : List (Attribute a f) -> List (Template a f) -> Template a f
div = CustomNode "div"

export
textinput : List (InputAttribute a f String) ->
              Template a f
textinput attrs = InputNode IText attrs


export
onchange : ((x:a) -> y -> f x) ->
             InputAttribute  a f y
onchange = OnChange

export
dynsetval : (a -> Maybe y) -> InputAttribute a f y
dynsetval = DynSetVal

export
text : List (Attribute a f) -> String -> Template a f
text = TextNode

export
dyntext : List (Attribute a f) -> (a -> String) ->
              Template a f
dyntext = DynTextNode

export
form : ((x:a) -> f x) -> List (Attribute a f) -> List (Template a f) -> Template a f
form = FormNode

export
foldTemplate : b -> (b->i->(b,Maybe r)) -> Template b (const i) -> List (FoldAttribute a f b r) -> Template a f
foldTemplate = FoldNode

export
listOnDiv : List (Attribute a f) -> (a -> List b) -> Template (a,b) (f . Prelude.Basics.fst) -> Template a f
listOnDiv = ListTemplateNode "div"

export
img : List (Attribute a f) -> String -> Template a f
img = ImgNode

export
style : IGen s a (List Style) => s -> Attribute a f
style x = StrAttribute "style" (map styleStr $ getGen x)

export
customNode : String -> List (Attribute a f) -> List (Template a f) -> Template a f
customNode = CustomNode
