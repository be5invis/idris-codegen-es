module Js.IO

||| Supported Python foreign types.
data JsTypes : Type -> Type where

  -- Primitive types
  JsInt     : JsTypes Int

FFI_Js : FFI
FFI_Js = MkFFI JsTypes String String

JSIO : Type -> Type
JSIO = IO' FFI_Js
