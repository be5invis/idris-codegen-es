module HtmlTemplate

import public Js.BrowserDom
import Js.ASync
import Effects

public export
data Style = MkStyle String String
           | CompStyle (List Style)

mutual
  styleStr' : Style -> String
  styleStr' (MkStyle k x) = k ++ ":" ++ x ++ ";"
  styleStr' (CompStyle x) = styleStr x

  export
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

export
IGen c b d => IGen c (DPair a (const b)) d where
  getGen {b} {d} x =
    case the (Gen b d) (getGen x) of
      GenConst z => GenConst z
      GenA fn => GenA $ \(_**y) => fn y

public export
data InputType = IText

public export
inputTypeTy : InputType -> Type
inputTypeTy IText = String

public export
data Attribute : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  EventClick : ((x:a) -> f x -> g x) -> Attribute a f g
  StrAttribute : String -> Gen (DPair a f) String -> Attribute a f g

public export
data InputAttribute : (a:Type) -> (a->Type) -> (a->Type) -> Type -> Type where
  GenAttr : Attribute a f g -> InputAttribute a f g c
  OnChange : ((x:a) -> c -> f x -> g x) -> InputAttribute a f g c
  SetVal : ((x:a) -> f x -> Maybe c) -> InputAttribute a f g c

public export
data FoldAttribute : (a:Type) -> (a->Type) -> (a->Type) -> (a->Type) -> (a -> Type) -> Type where
  OnEvent : DecEq a => ((x:a) -> f x -> r x -> g x) -> FoldAttribute a f g s r
  SetState : DecEq a => ((x:a) -> f x -> Maybe (s x)) -> FoldAttribute a f g s r

public export
data BTemplate : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  CustomNode : (DomNode -> JS_IO ()) -> String -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  TextNode : List (Attribute a f g) -> Gen (DPair a f) String -> BTemplate a f g
  InputNode : (t:InputType) -> List (InputAttribute a f g (inputTypeTy t)) ->
                  BTemplate a f g
--  FoldNode : DPair a f -> ((x:a) -> s x -> i x -> (s x, Maybe (r x))) -> ((x:a) -> (y:a) -> s x -> s y) ->
--              BTemplate a s i -> List (FoldAttribute a f g s r) -> BTemplate a f g
  FormNode : ((x:a) -> f x -> g x) -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  ListNode : String -> List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a h g -> BTemplate a f g
  ImgNode : List (Attribute a f g) -> Gen (DPair a f) String -> BTemplate a f g
--  ContraMapNode : (a -> b) -> BTemplate b (const c) -> BTemplate a (const c)
  EmptyNode : BTemplate a f g
  MaybeNode : String -> List (Attribute a f g) -> ((x:a)-> f x -> Maybe (h x)) -> BTemplate a h g -> BTemplate a f g
--  CaseNode : DecEq i => String -> List (Attribute a (const b)) -> (f : i -> Type) ->  (a->DPair i f) ->
--                          ((x:i) -> BTemplate (f x) (const b)) -> BTemplate a (const b)

GuiCallback : (a:Type) -> (a->Type) -> (a->Type) -> Type
GuiCallback a f g = JS_IO (x:a**(f x, g x -> JS_IO ()))

data Update : Type -> Type where
  MkUpdate : (a -> b) -> (b -> b -> JS_IO ()) -> Update a

Remove : Type
Remove = JS_IO ()

Updates : Type -> Type
Updates a = List (Update a)

mapUpdates : (a->b) -> (Remove, Updates b) -> (Remove, Updates a)
mapUpdates f (r,upds) = (r, map (\(MkUpdate g h)=>MkUpdate (g . f) h) upds)

procChange : {g:a->Type} -> GuiCallback a f g ->
                  (String -> c) -> ((x:a) -> c -> f x -> g x) -> String -> JS_IO ()
procChange gcb j h str =
  do
    (x**(y,pr)) <- gcb
    pr (h x (j str) y)

procClick : {g:a->Type} -> GuiCallback a f g -> ((x:a) -> f x -> g x) -> () -> JS_IO ()
procClick gcb h () =
  do
    (x**(y,pr)) <- gcb
    pr (h x y)

updateStrAttribute : DomNode -> String -> String -> String -> JS_IO ()
updateStrAttribute n name x1 x2 =
  if x1 == x2 then pure ()
    else setAttribute n (name, x2)

initAttribute : DPair a f -> DomNode -> GuiCallback a f g -> Attribute a f g -> JS_IO (Maybe (Update (DPair a f)))
initAttribute _ n gcb (EventClick h) =
  do
    registEvent (procClick gcb h) n "click" (pure ())
    pure Nothing
initAttribute _ n gcb (StrAttribute name (GenConst x) ) =
  do
    setAttribute n (name, x)
    pure Nothing
initAttribute v n gcb (StrAttribute name (GenA x) ) =
  do
    setAttribute n (name, x v)
    pure $ Just $ MkUpdate x (updateStrAttribute n name)

initAttributes : DPair a f -> DomNode -> GuiCallback a f g -> List (Attribute a f g) -> JS_IO (List (Update (DPair a f)))
initAttributes v n gcb attrs = (catMaybes<$>) $ sequence $ map (initAttribute v n gcb) attrs

procSetVal : DomNode -> Maybe String -> JS_IO ()
procSetVal _ Nothing = pure ()
procSetVal n (Just z) =
  setValue z n

initAttributeInp : DPair a f -> DomNode -> GuiCallback a f g ->
                      (String -> c) -> (c -> String) -> InputAttribute a f g c -> JS_IO (Maybe (Update (DPair a f)))
initAttributeInp v n gcb _ _ (GenAttr x) =
    initAttribute v n gcb x
initAttributeInp _ n gcb f _ (OnChange h) =
  do
    registEvent (procChange gcb f h) n "change" targetValue
    pure Nothing
initAttributeInp (x**y) n gcb _ f (SetVal h) =
  do
    procSetVal n (f <$> h x y)
    pure $ Just $ MkUpdate (\(x**y) => f <$> h x y) (\_,z=> procSetVal n z)

initAttributesInp : DPair a f -> DomNode -> GuiCallback a f g ->
                      (String -> y) -> (y -> String) -> List (InputAttribute a f g y) -> JS_IO (List (Update (DPair a f)))
initAttributesInp v n gcb f j attrs =
  (catMaybes<$>) $ sequence $ map (initAttributeInp v n gcb f j) attrs


procUpdate : a -> a -> Update a -> JS_IO ()
procUpdate old new (MkUpdate r u) =
  u (r old) (r new)

procUpdates : a -> a -> Updates a -> JS_IO ()
procUpdates oz z upds = sequence_ $ map (procUpdate oz z) upds


setState : JSIORef (Updates b) -> JSIORef b -> Maybe b -> Maybe b -> JS_IO ()
setState _ _ _ Nothing = pure ()
setState ctxU ctxS _ (Just z) =
  do
    oz <- readJSIORef ctxS
    writeJSIORef ctxS z
    upds <- readJSIORef ctxU
    procUpdates oz z upds
{-
procOnEvent : GuiCallback () (const c) (const b) -> r ->
                  List (FoldAttribute c b s r) -> JS_IO ()
procOnEvent _ _ [] =
  pure ()
procOnEvent gcb z ((OnEvent h)::r) =
  do
    (x**(y,pr)) <- gcb
    pr (h y z)
procOnEvent gcb z ((SetState h)::r) =
  procOnEvent gcb z r

calcFoldUpdatesList: JSIORef (Updates (x:()**s)) -> JSIORef (x:()**s) -> List (FoldAttribute c b s r) -> Updates (x:()**c)
calcFoldUpdatesList _ _ Nil = []
calcFoldUpdatesList x y ((OnEvent _)::r) = calcFoldUpdatesList x y r
calcFoldUpdatesList x y ((SetState h)::_) =
  [MkUpdate (\(()**z)=> (\w=>(()**w)) <$> h z  ) (setState x y)]


updateFold : JSIORef (Updates (x:()**s)) -> JSIORef (x:()**s) -> (s->i->(s,Maybe r)) ->
              GuiCallback () (const c) (const b) -> List (FoldAttribute c b s r) ->
               () -> i -> JS_IO ()
updateFold ctxU ctxS updfn gcb attrs _ e =
  do
    (()**st) <- readJSIORef ctxS
    let (newst, mr) = updfn st e
    writeJSIORef ctxS (()**newst)
    upds <- readJSIORef ctxU
    procUpdates (()**st) (()**newst) upds
    case mr of
      Nothing => pure ()
      Just x => procOnEvent gcb x attrs
-}

removeListNodes : List (Remove, Updates a) -> JS_IO ()
removeListNodes x =
  sequence_ $ map fst x

tmplLstConv : {h:a->Type} -> ((x:a) -> f x -> List (h x)) -> DPair a f -> List (DPair a h)
tmplLstConv genL (x**y) = map (\z => (x**z)) $ genL x y

convertGuiCallBack : DPair a h -> ((x:a) -> f x -> Maybe (h x)) -> GuiCallback a f g -> GuiCallback a h g
convertGuiCallBack (z**k) c gcb =
  do
    (x**(y,pr)) <- gcb
    case c x y of
      Nothing => pure (z**(k, \_=> pure() ))
      Just w => pure (x**(w, pr))

mutual

  updateListTemplate : Nat -> DomNode -> GuiCallback a f g -> ((x:a) -> f x -> List (h x)) ->
                              BTemplate a h g ->
                                List (DPair a h) -> List (DPair a h) ->
                                  List (Remove, Updates (DPair a h)) -> JS_IO (List (Remove, Updates (DPair a h)))
  updateListTemplate pos nd gcb h t (x::xs) (y::ys) ((r,u)::us) =
    do
      procUpdates x y u
      us' <- updateListTemplate (S pos) nd gcb h t xs ys us
      pure $ (r,u)::us'
  updateListTemplate pos nd gcb h t [] ys [] =
    addListNodes pos nd gcb h t ys
  updateListTemplate pos nd gcb h t xs [] us =
    do
      removeListNodes us
      pure []
  updateListTemplate pos nd gcb h t _ _ _ = pure []


  updateLT : DomNode -> GuiCallback a f g ->
              ((x:a) -> f x -> List (h x)) ->
                  BTemplate a h g -> JSIORef (List (Remove,Updates (DPair a h))) ->
                    DPair a f -> DPair a f -> JS_IO ()
  updateLT {a} {h} nd gcb genL t ctx o n =
    do
      upds <- readJSIORef ctx
      upds' <- updateListTemplate 0 nd gcb genL t (tmplLstConv genL o) (tmplLstConv genL n) upds
      writeJSIORef ctx upds'

  addListNodes : Nat -> DomNode -> GuiCallback a f g ->
                            ((x:a) -> f x -> List (h x)) ->
                              BTemplate a h g -> List (DPair a h) -> JS_IO (List (Remove, Updates (DPair a h)))
  addListNodes {a} {f} {h} pos nd gcb genL t [] = pure []
  addListNodes {a} {f} {h} pos nd gcb genL t (x::xs) =
    do
      us <- initTemplate' nd x (convertGuiCallBack x (\x,y=> index' pos $ genL x y) gcb) t --(convGCB x gcb) t
      us' <- addListNodes (S pos) nd gcb genL t xs
      pure $ us :: us'
{-    where
      convGCB : DPair a h -> GuiCallback a f g -> GuiCallback a h g
      convGCB (z**k) gcb =
        do
          (x**(y,pr)) <- gcb
          case index' pos $ genL x y of
            Nothing => pure (z**(k, \_=> pure() ))
            Just w => pure (x**(w, pr))-}

  updateMaybeNode : DomNode -> GuiCallback a f g -> JSIORef (Maybe (DPair a h,Remove, Updates (DPair a h))) -> BTemplate a h g ->
                      ((x:a)-> f x -> Maybe (h x)) -> (DPair a f) -> JS_IO ()
  updateMaybeNode n gcb ref t genM (y**v) =
    case (!(readJSIORef ref), genM y v) of
      (Nothing, Just w) =>
        do
          ru <- initTemplate' n (y**w) (convertGuiCallBack (y**w) genM gcb) t
          writeJSIORef ref $ Just ((y**w),ru)
      (Just (_,r,_), Nothing) =>
        do
          r
          writeJSIORef ref Nothing
      (Just (w,_,u), Just w') =>
          procUpdates w (y**w') u
      (Nothing, Nothing) =>
        pure ()

  removeMaybeNode : DomNode -> JSIORef (Maybe (DPair a h,Remove, Updates (DPair a h))) -> JS_IO ()
  removeMaybeNode n ref =
    case !(readJSIORef ref) of
      Nothing => pure ()
      Just (_,r,_) => r

  initChilds : DomNode -> DPair a f -> GuiCallback a f g ->
                  List (BTemplate a f g) -> JS_IO (Remove, Updates (DPair a f))
  initChilds n v gcb childs =
    do
      w <- (sequence $ map (initTemplate' n v gcb) childs)
      pure (sequence_ $ map fst w, concat $ map snd w)
{-
  updateCaseNode : DecEq i => DomNode -> (f : i -> Type) -> (a->DPair i f) -> JS_IO a ->
                                (b -> JS_IO ()) -> ((x:i) -> Template (f x) (const b)) ->
                                  JSIORef Remove -> JSIORef (DPair i (Updates . f)) -> Update a
  updateCaseNode n f h getst proc templs ctxR ctxU =
    MkUpdate id upd
    where
      updEq : (x:i) -> f x -> f x -> JS_IO ()
      updEq x y y' =
        do
          (x' ** upds) <- readJSIORef ctxU
          case decEq x x' of
            Yes Refl => procUpdates y y' upds
            No _ => pure ()

      getTheSt : (x:i) -> (f x) -> JS_IO (DPair i f) -> JS_IO (f x)
      getTheSt x z get =
        do
          (x' ** z') <- get
          case decEq x x' of
            Yes Refl => pure z'
            No _ => pure z

      upd' : DPair i f -> DPair i f -> JS_IO ()
      upd' (x ** z) (x' ** z') =
        case decEq x x' of
          Yes Refl => updEq x z z'
          No _ =>
            do
              r <- readJSIORef ctxR
              r
              (r', u) <- initTemplate' n z' (getTheSt x' z' (h <$> getst)) proc (templs x')
              writeJSIORef ctxR r'
              writeJSIORef ctxU (x' ** u)
      upd : a -> a -> JS_IO ()
      upd x y = upd' (h x) (h y)
-}

  initTemplate' : DomNode -> DPair a f -> GuiCallback a f g ->
                      BTemplate a f g -> JS_IO (Remove, Updates (DPair a f))
  initTemplate' n v gcb (CustomNode postProc tag attrs childs) =
    do
      newn <- appendNode n tag
      attrsUpds <- initAttributes v newn gcb attrs
      (cr, childsUpds) <- initChilds newn v gcb childs
      postProc newn
      pure (cr >>= \_ => removeDomNode newn, attrsUpds ++ childsUpds)
  initTemplate' n v gcb (TextNode attrs str) =
    do
      newn <- appendNode n "span"
      attrUpds <- initAttributes v newn gcb attrs
      case str of
        GenConst z =>
          do
            setText z newn
            pure (removeDomNode newn, attrUpds)
        GenA getter =>
          do
            setText (getter v) newn
            pure (removeDomNode newn, MkUpdate getter (\x,y => if x ==y then pure () else setText y newn) :: attrUpds)
  initTemplate' n v gcb (InputNode IText attrs) =
    do
      i <- appendNode n "input"
      setAttribute i ("type", "text")
      attrsUpds <- initAttributesInp v i gcb id id attrs
      pure (removeDomNode i, attrsUpds)
{-  initTemplate' n v gcb (FoldNode {c} {b} {s} {i} {r} s0 fupd t attrs) =
    do
      ctxS <- newJSIORef s0
      ctxU <- newJSIORef []
      (r, upds) <- initTemplate'
                n
                s0
                (readJSIORef ctxS)
                (updateFold {c=c} {b=b} {s=s} {i=i} ctxU ctxS fupd gcb attrs)
                t
      writeJSIORef ctxU upds
      pure (r, calcFoldUpdatesList ctxU ctxS attrs)-}
  initTemplate' n v gcb (FormNode submit attrs childs) =
    do
      frm <- appendNode n "form"
      registEvent (procClick gcb submit) frm "submit" preventDefault
      attrsUpds <- initAttributes v frm gcb attrs
      (cr, childsUpds) <- initChilds frm v gcb childs
      pure (cr >>= \_ => removeDomNode frm, attrsUpds ++ childsUpds)
  initTemplate' n v gcb (ListNode tag attrs genL t) =
    do
      newn <- appendNode n tag
      attrsUpds <- initAttributes v newn gcb attrs
      upds <- addListNodes 0 newn gcb genL t (tmplLstConv genL v)
      ctxU <- newJSIORef upds
      pure (readJSIORef ctxU >>= removeListNodes >>= \_ => removeDomNode newn
           , (MkUpdate id (updateLT newn gcb genL t ctxU)) :: attrsUpds)
  initTemplate' n v gcb (ImgNode attrs gen) =
    do
      nd <- appendNode n "img"
      attrsUpds <- initAttributes v nd gcb attrs
      case gen of
        GenConst x =>
          do
            setAttribute nd ("src", x)
            pure (removeDomNode nd, attrsUpds)
        GenA g =>
          do
            setAttribute nd ("src", g v)
            pure (removeDomNode nd, MkUpdate g (\x,y=> if x==y then pure () else setAttribute nd ("src", y)) :: attrsUpds)
--  initTemplate' n v getst proc (ContraMapNode f t) =
--    mapUpdates f <$> initTemplate' n (f v) (f <$> getst) proc t
  initTemplate' n v gcb EmptyNode =
    pure (pure (), [])
  initTemplate' n v gcb (MaybeNode tag attrs genM t) =
    do
      newn <- appendNode n tag
      ref <- newJSIORef Nothing
      attrsUpds <- initAttributes v newn gcb attrs
      updateMaybeNode n gcb ref t genM v
      pure (removeMaybeNode n ref >>= \_=>removeDomNode newn, [MkUpdate id (\o,new=> updateMaybeNode n gcb ref t genM new)])

{-  initTemplate' n v getst proc (CaseNode tag attrs f h templs) =
    do
      newn <- appendNode n tag
      attrsUpds <- initAttributes v newn getst proc attrs
      let (i**x) = h v
      ctxS <- newJSIORef x
      (r, upds) <- initTemplate' newn x (readJSIORef ctxS) proc (templs i)
      ctxUpds <- newJSIORef (i ** upds)
      ctxR <- newJSIORef r
      pure ( (join $ readJSIORef ctxR) >>= \_=>removeDomNode newn
           , (updateCaseNode newn f h getst proc templs ctxR ctxUpds) :: attrsUpds)
-}

export
data BGuiRef : (a:Type) -> (a->Type) -> (a->Type)-> a -> Type where
  MkBGuiRef : Updates (DPair a f) -> f x -> JSIORef (x:a**(f x, g x -> JS_IO ())) -> BGuiRef a f g x

export
data Html : Effect where
  InitBody : f x -> BTemplate a f g -> sig Html () () (BGuiRef a f g x)
  HtmlUpdate : (f x -> f y) -> sig Html () (BGuiRef a f g x) (BGuiRef a f g y)
  GetInput : sig Html (g x) (BGuiRef a f g x)

public export
HTML : (ty : Type) -> EFFECT
HTML t = MkEff t Html


initTemplate : DomNode -> f x -> BTemplate a f g -> JS_IO (BGuiRef a f g x)
initTemplate {a} {f} {g} {x} n v t =
  do
    gcb <- newJSIORef (x**(v,\_=>pure ()))
    (r, upds) <- initTemplate' n (x**v) (readJSIORef gcb) t
    pure $ MkBGuiRef upds v gcb

refreshTemplate : f y -> BGuiRef a f g x -> JS_IO (BGuiRef a f g y)
refreshTemplate {x} {y} w' (MkBGuiRef upds w gcb) =
  do
    procUpdates (x**w) (y**w') upds
    writeJSIORef gcb (y**(w',\_=>pure ()))
    pure $ MkBGuiRef upds w' gcb


readTemplate : BGuiRef a f g x -> f x
readTemplate (MkBGuiRef _ v _) = v


updateTemplate : (f x -> f y) -> BGuiRef a f g x -> JS_IO (BGuiRef a f g y)
updateTemplate f r = refreshTemplate (f (readTemplate r)) r


getInputTemplate : BGuiRef a f g x -> ASync (g x)
getInputTemplate {x} (MkBGuiRef _ v gcb) =
  MkASync $ \proc =>
    writeJSIORef gcb (x**(v,\w => do writeJSIORef gcb (x**(v,\_=> pure() )); proc w))


export
implementation Handler Html ASync where
  handle () (InitBody x t) k = do  b <- liftJS_IO body; r' <- liftJS_IO $ initTemplate b x t; k () r'
  handle r (HtmlUpdate f) k = do r' <- liftJS_IO $ updateTemplate f r; k () r'
  handle r GetInput k = do y <- getInputTemplate r; k y r


export
initBody : b -> BTemplate () (const b) (const c) -> Eff () [HTML ()] [HTML (BGuiRef () (const b) (const c) ())]
initBody x t = call $ InitBody x t

export
updateGui : (f x ->  f x) -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g x)]
updateGui h = call $ HtmlUpdate h

export
putGui : f x -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g x)]
putGui v = updateGui (const v)

export
getInput : Eff (g x) [HTML (BGuiRef a f g x)]
getInput = call GetInput

---------- Primitives -------------
{-
export
textinput : List (InputAttribute a f g String) ->
              Template a f
textinput attrs = InputNode IText attrs


export
onchange : (a -> c -> b) ->
             InputAttribute  a b c
onchange = OnChange

export
onclick : (a -> b) -> Attribute a b
onclick = EventClick

export
setval : (a -> Maybe y) -> InputAttribute a f y
setval = DynSetVal

export
text : IGen c a String => List (Attribute a f) -> c -> Template a f
text attrs x = TextNode attrs (getGen x)

export
form : (a -> b) -> List (Attribute a b) -> List (Template a b) -> Template a b
form = FormNode

export
foldTemplate : s -> (s->i->(s,Maybe r)) -> Template s i -> List (FoldAttribute a b s r) -> Template a b
foldTemplate = FoldNode

export
listOnDiv : List (Attribute a b) -> (a -> List c) -> Template c b -> Template a b
listOnDiv = ListNode "div"

export
img : IGen c a String => List (Attribute a f) -> c -> Template a f
img attrs x = ImgNode attrs (getGen x)

export
style : IGen s a (List Style) => s -> Attribute a f
style x = StrAttribute "style" (map styleStr $ getGen x)



infixl 4 >$<

export
(>$<) : (a->b) -> Template b c -> Template a c
(>$<) = ContraMapNode

export
emptyTemplate : Template a b
emptyTemplate = EmptyNode

export
caseTemplateSpan : DecEq i => List (Attribute a b) -> (f : i -> Type) ->  (a->DPair i f) ->
                          ((x:i) -> Template (f x) b) -> Template a b
caseTemplateSpan = CaseNode "span"
-}
