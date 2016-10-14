module Js.Arango
import Js.ASync

require : String -> JS_IO Ptr
require s = jscall "require(%0)" (String -> JS_IO Ptr) s

mkController : Ptr -> JS_IO Ptr
mkController fox = jscall  "new %0.Controller(applicationContext)" (Ptr -> JS_IO Ptr) fox

finstall_service : Ptr -> String -> (Ptr -> JS_IO () ) -> JS_IO ()
finstall_service ctrl name f =
  jscall
    "%0.post(%1, function(req,res){return %3([req,res])})"
    (Ptr -> String -> (JsFn (Ptr -> JS_IO ())) -> JS_IO () )
    ctrl
    name
    (MkJsFn f)

fget_serv_in : Ptr -> JS_IO String
fget_serv_in x = jscall "%0[0].rawBody()" (Ptr -> JS_IO String) x

fsend_res : Ptr -> String -> JS_IO ()
fsend_res x val = jscall "%0[1].send(%1)" (Ptr -> String -> JS_IO ()) x val

install_service : Ptr -> (String, String -> JS_IO String) -> JS_IO ()
install_service ctrl (name, f) =
  do
    finstall_service ctrl name nf
  where
    nf x = do
            inp <- fget_serv_in x
            res <- f inp
            fsend_res x res


export
install_services : List (String, String -> JS_IO String) -> JS_IO ()
install_services x = do
  foxx <- require "org/arangodb/foxx"
  ctrl <- mkController foxx
  traverse  (install_service ctrl) x
  pure ()
