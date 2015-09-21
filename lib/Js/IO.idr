module Js.IO

mutual
  data JsTypes : Type -> Type where
    JsInt     : JsTypes Int
    JsString  : JsTypes String
    JsPtr     : JsTypes Ptr
    JsUnit    : JsTypes ()
    JsFun     : JsTypes a -> JsTypes b -> JsTypes (a -> b)
    JsFunIO   : JsTypes a -> JsTypes b -> JsTypes (a -> (IO' FFI_Js) b)

  FFI_Js : FFI
  FFI_Js = MkFFI JsTypes String String

JSIO : Type -> Type
JSIO = IO' FFI_Js

%inline
jscall : (fname : String) -> (ty : Type) ->
          {auto fty : FTy FFI_Js [] ty} -> ty
jscall fname ty = foreign FFI_Js fname ty

