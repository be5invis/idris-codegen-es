module Js.HtmlUtils

import Js.HtmlTemplate
import Data.Vect

namespace Dependent
  public export
  Template : (a:Type) -> (a->Type) -> (a->Type) -> Type
  Template = BTemplate

  public export
  GuiRef : (a:Type) -> (a->Type) -> (a->Type)-> a -> Type
  GuiRef = BGuiRef

  export
  maybeOnSpanD : List (Attribute a f g) -> ((x:a)-> f x -> Maybe (h x)) -> BTemplate a h g -> BTemplate a f g
  maybeOnSpanD = MaybeNode "span"

  export
  listOnDivD : List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a h g -> BTemplate a f g
  listOnDivD = ListNode "div"

  export
  listOnDivIndexD : {h:a->Type} -> List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a (\x=> (Nat, h x)) g -> BTemplate a f g
  listOnDivIndexD attrs fn t = listOnDivD attrs (\x,y => let l = fn x y in zip [0..length l] l) t

  export
  vectOnDivIndex : {h:a->Type} -> List (Attribute a f g) -> (len : a->Nat) -> ((x:a) -> f x -> Vect (len x) (h x)) ->
                     BTemplate a (\x=>(Fin (len x), h x)) g -> BTemplate a f g
  vectOnDivIndex attrs len fn t = listOnDivD attrs (\x,y => let l = fn x y in toList $ zip range l) t

  export
  onclick : ((x:a) -> f x -> g x) -> Attribute a f g
  onclick = EventClick

  export
  onchange : ((x:a) -> f x -> c x -> g x) -> InputAttribute a f g c
  onchange = OnChange

  export
  form : ((x:a) -> f x -> g x) -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  form = FormNode

  infixl 4 >$<, <$>

  export
  (>$<) : ((x:a) -> h x -> f x) -> Template a f g -> Template a h g
  (>$<) a b = CMapNode a b

  export
  (<$>) : ((x:a) -> h x -> g x) -> Template a f h -> Template a f g
  (<$>) a b = MapNode a b

  export
  setVal : ((x:a) -> f x -> Maybe (c x)) -> InputAttribute a f g c
  setVal = SetVal

namespace Simple
  public export
  Template : {t:Type} -> Type -> Type -> Type
  Template {t} b c = BTemplate t (const b) (const c)

  public export
  GuiRef : Type -> Type -> Type
  GuiRef b c = BGuiRef () (const b) (const c) ()


  export
  maybeOnSpan : {t:Type} -> List (Attribute t (const b) (const c)) ->
                          (b -> Maybe d) -> BTemplate t (const d) (const c) -> BTemplate t (const b) (const c)
  maybeOnSpan attrs fn = MaybeNode "span" attrs (\_,y=> fn y)

  export
  listOnDiv : {t:Type} -> List (Attribute t (const b) (const c)) -> (b -> List d) ->
                          BTemplate t (const d) (const c) -> BTemplate t (const b) (const c)
  listOnDiv attrs fn = ListNode "div" attrs (\_,y=> fn y)

  export
  listOnDivIndex : {t:Type} -> List (Attribute t (const b) (const c)) -> (b -> List d) ->
                          BTemplate t (const (Nat, d)) (const c) -> BTemplate t (const b) (const c)
  listOnDivIndex {d} attrs fn = listOnDivIndexD {h=\_=>d} attrs (\_,y=> fn y)

  export
  onclick : {t:Type} -> (b -> c) -> Attribute t (const b) (const c)
  onclick fn = EventClick (\_,y=>fn y)

  export
  onclick' : {t:Type} -> c -> Attribute t (const b) (const c)
  onclick' x = onclick (const x)

  export
  onchange : {t:Type} -> (b -> c -> d) -> InputAttribute t (const b) (const d) (const c)
  onchange fn = OnChange (\_,x,y=> fn x y)


  export
  form : {t:Type} -> (b -> c) -> List (Attribute t (const b) (const c)) ->
            List (BTemplate t (const b) (const c)) -> BTemplate t (const b) (const c)
  form fn = FormNode (\_,x=>fn x)

  export
  form' : {t:Type} -> c -> List (Attribute t (const b) (const c)) ->
            List (BTemplate t (const b) (const c)) -> BTemplate t (const b) (const c)
  form' x = FormNode (\_,_=>x)

  export
  foldTemplate : ((x:a) -> s x) -> ((x:a) -> s x -> i x -> (s x, Maybe (r x))) -> ((x:a) -> (y:a) -> s x -> s y) ->
               BTemplate a s i -> List (FoldAttribute a f g s r) -> BTemplate a f g
  foldTemplate = FoldNode

  export
  setVal : {t:Type} -> (b -> Maybe c) -> InputAttribute t (const b) (const d) (const c)
  setVal fn = SetVal (\_,z=> fn z)

  export
  onchange' : {t:Type} -> (c -> d) -> InputAttribute t (const b) (const d) (const c)
  onchange' fn = OnChange (\_,_,x=> fn x)

export
dynD : (DPair a f -> b) -> Dyn (DPair a f) b
dynD x = DynA x

export
dyn : (c -> b) -> Dyn (DPair a (const c)) b
dyn x = DynA (\(_**y)=> x y)

export
textinput : List (InputAttribute a f g (const String)) ->
                BTemplate a f g
textinput = InputNode IText

export
text : IDyn t (DPair a f) String => List (Attribute a f g) -> t -> BTemplate a f g
text attrs txt = TextNode attrs (getDyn txt)

export
customNodeWidthPostProc : (DomNode -> GuiCallback a f g -> JS_IO d, d -> JS_IO ()) -> String ->
                            List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
customNodeWidthPostProc = CustomNode

export
customNode : String -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
customNode = CustomNode (\_,_=>pure (),\_=>pure ())

export
listCustom : String -> List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                        BTemplate a h g -> BTemplate a f g
listCustom = ListNode

export
img : IDyn u (DPair a f) String => List (Attribute a f g) -> u -> BTemplate a f g
img attrs url = customNode "img" (StrAttribute "src" (getDyn url) ::attrs) []

export
div : List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
div = customNode "div"

export
span : List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
span = customNode "span"


export
style : IDyn s (DPair a f) (List Style) => s -> Attribute a f g
style x = StrAttribute "style" (map styleStr $ getDyn x)

export
button : IDyn c (DPair a f) String => List (Attribute a f g) -> c -> BTemplate a f g
button attrs x = customNode "button" attrs [text [] x]
