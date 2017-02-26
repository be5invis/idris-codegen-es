module Cordova

import Js.Utils

export
onDeviceReady : JS_IO () -> JS_IO ()
onDeviceReady x =
  jscall "document.addEventListener('deviceready', %0, false)" (JsFn (() -> JS_IO ()) -> JS_IO ()) (MkJsFn (\() => x))
