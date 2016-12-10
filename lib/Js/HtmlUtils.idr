module Js.HtmlUtils

import Js.HtmlTemplate

namespace Dependent
  public export
  Template : (a:Type) -> (a->Type) -> (a->Type) -> Type
  Template = BTemplate

  public export
  GuiRef : (a:Type) -> (a->Type) -> (a->Type)-> a -> Type
  GuiRef = BGuiRef

  export
  maybeOnSpan : List (Attribute a f g) -> ((x:a)-> f x -> Maybe (h x)) -> BTemplate a h g -> BTemplate a f g
  maybeOnSpan = MaybeNode "span"

  export
  listOnDiv : List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a h g -> BTemplate a f g
  listOnDiv = ListNode "div"

  export
  listOnDivIndex : {h:a->Type} -> List (Attribute a f g) -> ((x:a) -> f x -> List (h x)) ->
                          BTemplate a (\x=> (Nat, h x)) g -> BTemplate a f g
  listOnDivIndex attrs fn t = listOnDiv attrs (\x,y => let l = fn x y in zip [0..length l] l) t

  export
  onclick : ((x:a) -> f x -> g x) -> Attribute a f g
  onclick = EventClick

  export
  onchange : ((x:a) -> c -> f x -> g x) -> InputAttribute a f g c
  onchange = OnChange

  export
  form : ((x:a) -> f x -> g x) -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
  form = FormNode

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
  listOnDivIndex {d} attrs fn = listOnDivIndex {h=\_=>d} attrs (\_,y=> fn y)

  export
  onclick : {t:Type} -> (b -> c) -> Attribute t (const b) (const c)
  onclick fn = EventClick (\_,y=>fn y)

  export
  onclick' : {t:Type} -> c -> Attribute t (const b) (const c)
  onclick' x = onclick (const x)

  export
  onchange : {t:Type} -> (c -> b -> d) -> InputAttribute t (const b) (const d) c
  onchange fn = OnChange (\_,x,y=> fn x y)

  export
  onchange' : {t:Type} -> (c -> d) -> InputAttribute t (const b) (const d) c
  onchange' fn = OnChange (\_,x,_=> fn x)

  export
  form : {t:Type} -> (b -> c) -> List (Attribute t (const b) (const c)) ->
            List (BTemplate t (const b) (const c)) -> BTemplate t (const b) (const c)
  form fn = FormNode (\_,x=>fn x)

  export
  form' : {t:Type} -> c -> List (Attribute t (const b) (const c)) ->
            List (BTemplate t (const b) (const c)) -> BTemplate t (const b) (const c)
  form' x = FormNode (\_,_=>x)


export
textinput : List (InputAttribute a f g String) ->
                BTemplate a f g
textinput = InputNode IText

export
text : IGen t (DPair a f) String => List (Attribute a f g) -> t -> BTemplate a f g
text attrs txt = TextNode attrs (getGen txt)

export
img : IGen u (DPair a f) String => List (Attribute a f g) -> u -> BTemplate a f g
img attrs url = ImgNode attrs (getGen url)

export
customNodeWidthPostProc : (DomNode -> JS_IO ()) -> String -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
customNodeWidthPostProc = CustomNode

export
customNode : String -> List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
customNode = CustomNode (\_=>pure ())

export
div : List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
div = customNode "div"

export
span : List (Attribute a f g) -> List (BTemplate a f g) -> BTemplate a f g
span = customNode "span"


export
style : IGen s (DPair a f) (List Style) => s -> Attribute a f g
style x = StrAttribute "style" (map styleStr $ getGen x)

export
button : IGen c (DPair a f) String => List (Attribute a f g) -> c -> BTemplate a f g
button attrs x = customNode "button" attrs [text [] x]
