module HtmlTemplate

import public Js.BrowserDom
import Js.ASync
import Effects

export
doubleToString : Double -> String
doubleToString = show


public export
data Dyn a b = DynConst b | DynA (a->b)

public export
interface IDyn c a b where
  getDyn : c -> Dyn a b

export
IDyn b a b where
  getDyn x = DynConst x

export
Functor (Dyn a) where
  map f (DynConst x) = DynConst (f x)
  map f (DynA x) = DynA (f . x)

export
Applicative (Dyn a) where
  pure = DynConst

  (<*>) (DynConst f) fa = f <$> fa
  (<*>) (DynA f) (DynA fa) = DynA (\x => (f x) (fa x))
  (<*>) (DynA f) (DynConst fa) = DynA (\x => (f x) fa)

export
IDyn (Dyn a b) a b where
  getDyn x = x

export
IDyn Integer a Double where
  getDyn x = DynConst (fromInteger x)

export
data AnimationOption : Type where
  Duration : Nat -> AnimationOption

readAnimationOptions : List AnimationOption -> AnimationConfig
readAnimationOptions [] = MkAnimationConfig 0 Both
readAnimationOptions ((Duration d)::r) = record {duration = d} $ readAnimationOptions r

export
duration : Nat -> AnimationOption
duration = Duration


public export
data InputType = IText

public export
InputTypeTy : InputType -> (a -> Type)
InputTypeTy IText = const String

public export
data BAttribute : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  EventClick : ((x:a) -> f x -> g x) -> BAttribute a f g
  StrAttribute : Maybe String -> String -> Dyn (DPair a f) String -> BAttribute a f g
  CSSAttribute : String -> Dyn (DPair a f) String -> BAttribute a f g
  EventLongPress : ((x:a) -> f x -> g x) -> BAttribute a f g
  EventShortPress : ((x:a) -> f x -> g x) -> BAttribute a f g
  GroupAttribute : List (BAttribute a f g) -> BAttribute a f g

public export
data InputAttribute : (a:Type) -> (a->Type) -> (a->Type) -> (a-> Type) -> Type where
  GenAttr : BAttribute a f g -> InputAttribute a f g c
  OnChange : ((x:a) -> f x -> c x -> g x) -> InputAttribute a f g c
  SetVal : ((x:a) -> f x -> Maybe (c x)) -> InputAttribute a f g c

public export
data FoldAttribute : (a:Type) -> (a->Type) -> (a->Type) -> (a->Type) -> (a -> Type) -> Type where
  OnEvent : ((x:a) -> f x -> r x -> g x) -> FoldAttribute a f g s r
  SetState : ((x:a) -> f x -> Maybe (s x)) -> FoldAttribute a f g s r

public export
GuiCallback : (a:Type) -> (a->Type) -> (a->Type) -> Type
GuiCallback a f g = JS_IO (x:a**(f x, g x -> JS_IO ()))

public export
data BTemplate : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  CustomNode : Maybe String -> String -> (DomNode -> GuiCallback a f g -> JS_IO d, d -> JS_IO ()) ->
                  List (BAttribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  TextNode : Maybe String -> String -> List (BAttribute a f g) -> Dyn (DPair a f) String -> BTemplate a f g
  InputNode : (t:InputType) -> List (InputAttribute a f g (InputTypeTy t)) ->
                  BTemplate a f g
  FoldNode : ((x:a) -> s x) -> ((x:a) -> s x -> i x -> (s x, Maybe (r x))) -> ((x:a) -> (y:a) -> s x -> s y) ->
               BTemplate a s i -> List (FoldAttribute a f g s r) -> BTemplate a f g
  FormNode : ((x:a) -> f x -> g x) -> List (BAttribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  ListNode : Maybe String -> String -> List (BAttribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a h g -> BTemplate a f g
  EmptyNode : BTemplate a f g
  MaybeNode : String -> List (BAttribute a f g) -> ((x:a)-> f x -> Maybe (h x)) -> BTemplate a h g -> BTemplate a f g
  MapNode : ((x:a) -> g x -> h x) -> BTemplate a f g -> BTemplate a f h
  CMapNode : ((x:a) -> h x -> f x) -> BTemplate a f g -> BTemplate a h g

data AnimationTransition = CSSChange DomNode (List (String, String, String))

data Update : Type -> Type where
  MkUpdate : (a -> b) -> (b -> b -> JS_IO (List AnimationTransition)) -> Update a

Remove : Type
Remove = JS_IO ()

Updates : Type -> Type
Updates a = List (Update a)

mapUpdates : (a->b) -> (Remove, Updates b) -> (Remove, Updates a)
mapUpdates f (r,upds) = (r, map (\(MkUpdate g h)=>MkUpdate (g . f) h) upds)

procChange : {g:a->Type} -> {c:a->Type} -> GuiCallback a f g ->
                  ((x:a) -> String -> c x) -> ((x:a) -> f x -> c x -> g x) -> String -> JS_IO ()
procChange gcb j h str =
  do
    (x**(y,pr)) <- gcb
    pr (h x y (j x str))

export
procClick : {g:a->Type} -> GuiCallback a f g -> ((x:a) -> f x -> g x) -> () -> JS_IO ()
procClick gcb h () =
  do
    (x**(y,pr)) <- gcb
    pr (h x y)

procClickIf : {g:a->Type} -> JSIORef Bool -> GuiCallback a f g -> ((x:a) -> f x -> g x) -> () -> JS_IO ()
procClickIf ref gcb h () =
    if !(readJSIORef ref) then procClick gcb h ()
      else pure ()


updateStrAttribute : Maybe String -> DomNode -> String -> String -> String -> JS_IO (List AnimationTransition)
updateStrAttribute ns n name x1 x2 =
  if x1 == x2 then pure []
    else do
      setAttributeNS ns n (name, x2)
      pure []

initAttribute : DPair a f -> DomNode -> GuiCallback a f g -> BAttribute a f g -> JS_IO (List (Update (DPair a f)))
initAttribute _ n gcb (EventClick h) =
  do
    registEvent (procClick gcb h) n "click" (pure ())
    pure []
initAttribute _ n gcb (EventLongPress h) =
  do
    ref <- newJSIORef False
    registEvent
      (\() => (writeJSIORef ref True >>= \_=> setTimeout (procClickIf ref gcb h ()) 600)) n "mousedown" (pure ())
    registEvent (\()=>writeJSIORef ref False) n "mouseup" (pure ())
    pure []
initAttribute _ n gcb (EventShortPress h) =
  do
    ref <- newJSIORef False
    registEvent (\() => (writeJSIORef ref True >>= \_=> setTimeout (writeJSIORef ref False) 500)) n "mousedown" (pure ())
    registEvent (procClickIf ref gcb h) n "mouseup" (pure ())
    pure []
initAttribute _ n gcb (StrAttribute ns name (DynConst x) ) =
  do
    setAttributeNS ns n (name, x)
    pure []
initAttribute v n gcb (StrAttribute ns name (DynA x) ) =
  do
    setAttributeNS ns n (name, x v)
    pure $ [MkUpdate x (updateStrAttribute ns n name)]
initAttribute v n gcb (CSSAttribute name (DynConst x)) =
  do
    setCSSProp n name x
    pure []
initAttribute v n gcb (CSSAttribute name (DynA f)) =
  do
    setCSSProp n name (f v)
    pure $ [MkUpdate f (\x,y=> if x == y then pure [] else pure $ [CSSChange n [(name, x,y)]])]
initAttribute v n gcb (GroupAttribute attrs) =
  (join<$>) $ sequence $ map (initAttribute v n gcb) attrs

initAttributes : DPair a f -> DomNode -> GuiCallback a f g -> List (BAttribute a f g) -> JS_IO (List (Update (DPair a f)))
initAttributes v n gcb attrs = initAttribute v n gcb $ GroupAttribute attrs

procSetVal : DomNode -> Maybe String -> JS_IO ()
procSetVal _ Nothing = pure ()
procSetVal n (Just z) =
  setValue z n

initAttributeInp : DPair a f -> DomNode -> GuiCallback a f g ->
                      ((x:a) -> String -> c x) -> ((x:a) -> c x -> String) -> InputAttribute a f g c -> JS_IO (List (Update (DPair a f)))
initAttributeInp v n gcb _ _ (GenAttr x) =
    initAttribute v n gcb x
initAttributeInp _ n gcb f _ (OnChange h) =
  do
    registEvent (procChange gcb f h) n "change" targetValue
    pure []
initAttributeInp (x**y) n gcb _ f (SetVal h) =
  do
    procSetVal n (f x <$> h x y)
    pure $ [MkUpdate (\(x**y) => f x <$> h x y) (\_,z=> do procSetVal n z; pure [])]

initAttributesInp : DPair a f -> DomNode -> GuiCallback a f g ->
                      ((x:a) -> String -> y x) -> ((x:a) -> y x -> String) -> List (InputAttribute a f g y) -> JS_IO (List (Update (DPair a f)))
initAttributesInp v n gcb f j attrs =
  (join<$>) $ sequence $ map (initAttributeInp v n gcb f j) attrs


procUpdate : a -> a -> Update a -> JS_IO (List AnimationTransition)
procUpdate old new (MkUpdate r u) =
  u (r old) (r new)

procUpdates : a -> a -> Updates a -> JS_IO (List AnimationTransition)
procUpdates oz z upds = (join <$>) $ sequence $ map (procUpdate oz z) upds


procOnEvent : (x:a) -> f x -> r x -> (g x -> JS_IO ()) -> List (FoldAttribute a f g s r) -> JS_IO ()
procOnEvent z m n fn [] = pure ()
procOnEvent z m n fn (SetState _::r) = procOnEvent z m n fn r
procOnEvent z m n fn (OnEvent h::_) = fn (h z m n)


getSetState : List (FoldAttribute a f g s r) -> ((x:a) -> f x -> Maybe (s x))
getSetState [] = \_,_=>Nothing
getSetState (OnEvent _::r) = getSetState r
getSetState (SetState h::_) = h

foldGCB : ((x:a) -> (y:a) -> s x -> s y) -> ((x:a) -> s x -> i x -> (s x, Maybe (r x))) ->
            List (FoldAttribute a f g s r) ->
            JSIORef (DPair a s) -> GuiCallback a f g -> GuiCallback a s i
foldGCB {a} {f} {g} {s} {r} {i} updParam upd attrs stateRef mainGCB =
  do
    (x**v) <- readJSIORef stateRef
    (y**(m,fn)) <- mainGCB
    let v' = updParam x y v
    pure (y**(v', proc y v' m fn))
  where
    proc : (x:a) -> s x -> f x -> (g x -> JS_IO()) -> i x -> JS_IO ()
    proc z st m fn v =
      do
        let (news, res) = upd z st v
        writeJSIORef stateRef (z**news)
        case res of
          Nothing =>
            pure ()
          Just w =>
            procOnEvent z m w fn attrs

foldUpd : ((x:a) -> (y:a) -> s x -> s y) -> JSIORef (Updates (DPair a s))-> JSIORef (DPair a s) ->
            ((x:a) -> f x -> Maybe (s x)) -> Update (DPair a f)
foldUpd updParam refUpds refSt fn =
  MkUpdate id upd
  where
    upd _ (z**v) =
      do
        (y**oldSt) <- readJSIORef refSt
        newSt <-
          case fn z v of
            Nothing =>
              pure (updParam y z oldSt)
            Just w =>
              pure w
        upds <- readJSIORef refUpds
        procUpdates (y**oldSt) (z**newSt) upds


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

mapGuiCallBack : ((x:a) -> g x -> h x) -> GuiCallback a f h -> GuiCallback a f g
mapGuiCallBack fn gcb =
  do
    (x**(y,pr)) <- gcb
    pure (x**(y, \k=>pr $ fn x k))

cMapGuiCallBack : ((x:a) -> h x -> f x) -> GuiCallback a h g -> GuiCallback a f g
cMapGuiCallBack fn gcb =
  do
    (x**(y,pr)) <- gcb
    pure (x**(fn x y, pr))

mutual

  updateListTemplate : Nat -> DomNode -> GuiCallback a f g -> ((x:a) -> f x -> List (h x)) ->
                              BTemplate a h g ->
                                List (DPair a h) -> List (DPair a h) ->
                                  List (Remove, Updates (DPair a h)) -> JS_IO (List (Remove, Updates (DPair a h)), List AnimationTransition)
  updateListTemplate pos nd gcb h t (x::xs) (y::ys) ((r,u)::us) =
    do
      csstru <-procUpdates x y u
      (us', csstrus) <- updateListTemplate (S pos) nd gcb h t xs ys us
      pure $ ((r,u)::us', csstru ++ csstrus)
  updateListTemplate pos nd gcb h t [] ys [] =
    do
      u <- addListNodes pos nd gcb h t ys
      pure (u,[])
  updateListTemplate pos nd gcb h t xs [] us =
    do
      removeListNodes us
      pure ([],[])
  updateListTemplate pos nd gcb h t _ _ _ = pure ([],[])


  updateLT : DomNode -> GuiCallback a f g ->
              ((x:a) -> f x -> List (h x)) ->
                  BTemplate a h g -> JSIORef (List (Remove,Updates (DPair a h))) ->
                    DPair a f -> DPair a f -> JS_IO (List AnimationTransition)
  updateLT {a} {h} nd gcb genL t ctx o n =
    do
      upds <- readJSIORef ctx
      (upds', csstr) <- updateListTemplate 0 nd gcb genL t (tmplLstConv genL o) (tmplLstConv genL n) upds
      writeJSIORef ctx upds'
      pure csstr

  addListNodes : Nat -> DomNode -> GuiCallback a f g ->
                            ((x:a) -> f x -> List (h x)) ->
                              BTemplate a h g -> List (DPair a h) -> JS_IO (List (Remove, Updates (DPair a h)))
  addListNodes {a} {f} {h} pos nd gcb genL t [] = pure []
  addListNodes {a} {f} {h} pos nd gcb genL t (x::xs) =
    do
      us <- initTemplate' nd x (convertGuiCallBack x (\x,y=> index' pos $ genL x y) gcb) t
      us' <- addListNodes (S pos) nd gcb genL t xs
      pure $ us :: us'

  updateMaybeNode : DomNode -> GuiCallback a f g -> JSIORef (Maybe (DPair a h,Remove, Updates (DPair a h))) -> BTemplate a h g ->
                      ((x:a)-> f x -> Maybe (h x)) -> (DPair a f) -> JS_IO (List AnimationTransition)
  updateMaybeNode n gcb ref t genM (y**v) =
    case (!(readJSIORef ref), genM y v) of
      (Nothing, Just w) =>
        do
          ru <- initTemplate' n (y**w) (convertGuiCallBack (y**w) genM gcb) t
          writeJSIORef ref $ Just ((y**w),ru)
          pure []
      (Just (_,r,_), Nothing) =>
        do
          r
          writeJSIORef ref Nothing
          pure []
      (Just (w,_,u), Just w') =>
          procUpdates w (y**w') u
      (Nothing, Nothing) =>
        pure []

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

  initTemplate' : DomNode -> DPair a f -> GuiCallback a f g ->
                      BTemplate a f g -> JS_IO (Remove, Updates (DPair a f))
  initTemplate' n v gcb (CustomNode ns tag (postProc, onRemove) attrs childs) =
    do
      newn <- appendNodeNS n ns tag
      attrsUpds <- initAttributes v newn gcb attrs
      (cr, childsUpds) <- initChilds newn v gcb childs
      or <- postProc newn gcb
      pure (onRemove or >>= \_=> cr >>= \_ => removeDomNode newn, attrsUpds ++ childsUpds)
  initTemplate' n v gcb (TextNode ns tag attrs str) =
    do
      newn <- appendNodeNS n ns tag
      attrUpds <- initAttributes v newn gcb attrs
      case str of
        DynConst z =>
          do
            setText z newn
            pure (removeDomNode newn, attrUpds)
        DynA getter =>
          do
            setText (getter v) newn
            pure (removeDomNode newn, MkUpdate getter (\x,y => if x ==y then pure [] else do setText y newn; pure []) :: attrUpds)
  initTemplate' n v gcb (InputNode IText attrs) =
    do
      i <- appendNode n "input"
      setAttribute i ("type", "text")
      attrsUpds <- initAttributesInp v i gcb (\_,x=>x) (\_,x=>x) attrs
      pure (removeDomNode i, attrsUpds)
  initTemplate' n (y**v) gcb (FoldNode {a} {s} s0 upd updParam t attrs) =
    do
      let setSt = getSetState attrs
      let s0' =
        case setSt y v of
          Nothing => s0 y
          Just w => w
      ctxS <- newJSIORef (y**s0')
      ctxU <- newJSIORef $ the (Updates (DPair a s)) Prelude.List.Nil
      (r, upds) <- initTemplate'
                n
                (y**s0')
                (foldGCB updParam upd attrs ctxS gcb)
                t
      writeJSIORef ctxU upds
      pure (r, [foldUpd updParam ctxU ctxS setSt])
  initTemplate' n v gcb (FormNode submit attrs childs) =
    do
      frm <- appendNode n "form"
      registEvent (procClick gcb submit) frm "submit" preventDefault
      attrsUpds <- initAttributes v frm gcb attrs
      (cr, childsUpds) <- initChilds frm v gcb childs
      pure (cr >>= \_ => removeDomNode frm, attrsUpds ++ childsUpds)
  initTemplate' n v gcb (ListNode ns tag attrs genL t) =
    do
      newn <- appendNodeNS n ns tag
      attrsUpds <- initAttributes v newn gcb attrs
      upds <- addListNodes 0 newn gcb genL t (tmplLstConv genL v)
      ctxU <- newJSIORef upds
      pure (readJSIORef ctxU >>= removeListNodes >>= \_ => removeDomNode newn
           , (MkUpdate id (updateLT newn gcb genL t ctxU)) :: attrsUpds)
  initTemplate' n v gcb EmptyNode =
    pure (pure (), [])
  initTemplate' n v gcb (MaybeNode tag attrs genM t) =
    do
      newn <- appendNode n tag
      ref <- newJSIORef Nothing
      attrsUpds <- initAttributes v newn gcb attrs
      updateMaybeNode n gcb ref t genM v
      pure (removeMaybeNode n ref >>= \_=>removeDomNode newn, [MkUpdate id (\o,new=> updateMaybeNode n gcb ref t genM new)])
  initTemplate' n v gcb (MapNode fn tmpl) =
    initTemplate' n v (mapGuiCallBack fn gcb) tmpl
  initTemplate' n (x**v) gcb (CMapNode fn tmpl) =
    do
      ru <- initTemplate' n (x**(fn x v)) (cMapGuiCallBack fn gcb) tmpl
      pure (mapUpdates (\(x**w)=>(x**(fn x w))) ru)

{-
export
data BGuiRef : (a:Type) -> (a->Type) -> (a->Type)-> a -> Type where
  MkBGuiRef : Updates (DPair a f) -> JSIORef (f x) ->
                JSIORef (g x -> JS_IO ()) ->
                  ((z:a) -> f z -> (Double, Double) -> f z) ->
                    BGuiRef a f g x
-}

export
data BGuiRef : (a:Type) -> (a->Type) -> (a->Type)-> a -> Type where
  MkBGuiRef : Updates (DPair a f) -> JSIORef (f x) ->
                JSIORef (z:a ** (JSIORef (f z), g z -> JS_IO ()) ) ->
                  JSIORef (z:a ** (JSIORef (f z))) ->
                    BGuiRef a f g x


emptyGCB : {a:Type} -> {f:a->Type} -> {g:a->Type} -> {x:a} -> JSIORef (f x) -> (z:a ** (JSIORef (f z), g z -> JS_IO ()) )
emptyGCB {x} v = (x**(v, \_=>pure ()))


-- GuiCallback a f g = JS_IO (x:a**(f x, g x -> JS_IO ()))
getGuiCallBack : JSIORef (z:a ** (JSIORef (f z), g z -> JS_IO ()) ) -> GuiCallback a f g
getGuiCallBack gcb' =
  do
    (x**(st, c)) <- readJSIORef gcb'
    s <- readJSIORef st
    pure (x**(s, c))


export
data HtmlOption : (a:Type) -> (a->Type) -> (a->Type) -> Type where
  OnResize : ((x:a) -> f x -> (Double, Double) -> f x) -> HtmlOption a f g

export
onResize : ((x:a) -> f x -> (Double, Double) -> f x) -> HtmlOption a f g
onResize = OnResize

export
data Html : Effect where
  InitBody : List (HtmlOption a f g) -> f x -> BTemplate a f g -> sig Html () () (BGuiRef a f g x)
  HtmlUpdate : (f x -> f y) -> sig Html () (BGuiRef a f g x) (BGuiRef a f g y)
  HtmlAnimate : List AnimationOption -> (f x -> f y) -> sig Html () (BGuiRef a f g x) (BGuiRef a f g y)
  GetInput : sig Html (g x) (BGuiRef a f g x)
  ConsoleLog : String -> sig Html () a
  Wait : Nat -> sig Html () a

public export
HTML : (ty : Type) -> EFFECT
HTML t = MkEff t Html

applyTransition : AnimationTransition -> JS_IO ()
applyTransition (CSSChange n l) =
  do
    let la = the (List (JS_IO ())) $ map (\(name,_,new)=>setCSSProp n name new) l
    sequence_ la

animTransition : AnimationConfig -> AnimationTransition -> JS_IO ()
animTransition aConf (CSSChange n l) =
  animateCSS aConf n [map (\(name,x,_) => (name,x)) l, map (\(name,_,x)=> (name,x)) l]

doUpdates : List AnimationOption -> a -> a -> Updates a -> JS_IO ()
doUpdates lo x y u =
  do
    animtrs <- procUpdates x y u
    let animConf = readAnimationOptions lo
    if duration animConf == 0 then
      sequence_ $ map applyTransition animtrs
      else
        sequence_ $ map (animTransition animConf) animtrs

onResizeFn : Updates (DPair a f) -> JSIORef (z:a ** (JSIORef (f z))) -> ((x:a) -> f x -> (Double, Double) -> f x) -> () -> JS_IO ()
onResizeFn upds ref h () =
  do
    width <- jscall "window.innerWidth" (() -> JS_IO Double) ()
    height <- jscall "window.innerHeight" (() -> JS_IO Double) ()
    (x**sRef) <- readJSIORef ref
    s <- readJSIORef sRef
    let s' = h x s (width,height)
    writeJSIORef sRef s'
    doUpdates [] (x**s) (x**s') upds

setOnResize : Updates (DPair a f) -> JSIORef (z:a ** (JSIORef (f z))) -> ((x:a) -> f x -> (Double, Double) -> f x) -> JS_IO ()
setOnResize upds ref h =
  do
    onResizeFn upds ref h ()
    jscall
      "window.onresize = %0"
      (JsFn (() -> JS_IO ()) -> JS_IO ())
      (MkJsFn $ onResizeFn upds ref h)


initOnResizeOpt : Updates (DPair a f) -> JSIORef (z:a ** (JSIORef (f z))) -> List (HtmlOption a f g) -> JS_IO ()
initOnResizeOpt upds stRef [] = pure ()
initOnResizeOpt upds stRef (OnResize h::_) = setOnResize upds stRef h
initOnResizeOpt upds stRef (_::r) = initOnResizeOpt upds stRef r


initTemplate : List (HtmlOption a f g) -> DomNode -> f x -> BTemplate a f g -> JS_IO (BGuiRef a f g x)
initTemplate {a} {f} {g} {x} opts n v t =
  do
    st <- newJSIORef v
    gcb <- newJSIORef (emptyGCB st)
    stRef <- the (JS_IO ( JSIORef (z:a ** (JSIORef (f z))))) $ newJSIORef (x**st)
    (r, upds) <- initTemplate' n (x**v) (getGuiCallBack gcb) t
    initOnResizeOpt upds stRef opts
    pure $ MkBGuiRef upds st gcb stRef

refreshTemplate : List AnimationOption -> f y -> BGuiRef a f g x -> JS_IO (BGuiRef a f g y)
refreshTemplate {x} {y} aOpts wv' (MkBGuiRef upds w gcb rcb) =
  do
    wv <- readJSIORef w
    doUpdates aOpts (x**wv) (y**wv') upds
    w' <- newJSIORef wv'
    writeJSIORef gcb (emptyGCB w')
    writeJSIORef rcb (y**w')
    pure $ MkBGuiRef upds w' gcb rcb


readTemplate : BGuiRef a f g x -> JS_IO (f x)
readTemplate (MkBGuiRef _ v _ _) = readJSIORef v


updateTemplate : List AnimationOption -> (f x -> f y) -> BGuiRef a f g x -> JS_IO (BGuiRef a f g y)
updateTemplate aOpts f r = refreshTemplate aOpts (f !(readTemplate r)) r

getInputTemplate : BGuiRef a f g x -> ASync (g x)
getInputTemplate {x} (MkBGuiRef _ v gcb rcb) =
  MkASync $ \proc =>
    writeJSIORef gcb (x**(v,(\w => do writeJSIORef gcb (emptyGCB v); proc w)))


export
implementation Handler Html ASync where
  handle () (InitBody opts x t) k = do  b <- liftJS_IO body; r' <- liftJS_IO $ initTemplate opts b x t; k () r'
  handle r (HtmlUpdate f) k = do r' <- liftJS_IO $ updateTemplate [] f r; k () r'
  handle r (HtmlAnimate opts f) k = do r' <- liftJS_IO $ updateTemplate opts f r; k () r'
  handle r GetInput k = do y <- getInputTemplate r; k y r
  handle r (ConsoleLog s) k = do liftJS_IO $ putStr' s; k () r
  handle r (Wait millis) k = do do setTimeout (cast millis) (); k () r


export
initBody : List (HtmlOption () (const b) (const c)) -> b -> BTemplate () (const b) (const c) -> Eff () [HTML ()] [HTML (BGuiRef () (const b) (const c) ())]
initBody opts x t = call $ InitBody opts x t

export
initBodyM : List (HtmlOption a f g) -> f x -> BTemplate a f g -> Eff () [HTML ()] [HTML (BGuiRef a f g x)]
initBodyM opts x t = call $ InitBody opts x t

export
updateGui : (f x ->  f x) -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g x)]
updateGui h = call $ HtmlUpdate h

export
animateGui : List AnimationOption -> (f x ->  f x) -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g x)]
animateGui opts h = call $ HtmlAnimate opts h

export
updateGuiM : (f x ->  f y) -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g y)]
updateGuiM h = call $ HtmlUpdate h

export
putGui : f x -> Eff () [HTML (BGuiRef a f g x)] [HTML (BGuiRef a f g x)]
putGui v = updateGui (const v)

export
getInput : Eff (g x) [HTML (BGuiRef a f g x)]
getInput = call GetInput

export
consoleLog : String -> Eff () [HTML a]
consoleLog s = call $ ConsoleLog s

export
wait : Nat -> Eff () [HTML a]
wait millis = call $ Wait millis
