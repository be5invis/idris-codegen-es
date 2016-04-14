module Js.Arango
import Js.IO

require : String -> JSIO Ptr
require s = jscall "require(%0)" (String -> JSIO Ptr) s

mkController : Ptr -> JSIO Ptr
mkController fox = jscall  "new %0.Controller(applicationContext)" (Ptr -> JSIO Ptr) fox

finstall_service : Ptr -> String -> (Ptr -> JSIO () ) -> JSIO ()
finstall_service ctrl name f =
  jscall
    "%0.post(%1, function(req,res){return %3([req,res])})"
    (Ptr -> String -> (Ptr -> JSIO ()) -> JSIO () )
    ctrl
    name
    f

fget_serv_in : Ptr -> JSIO String
fget_serv_in x = jscall "%0[0].rawBody()" (Ptr -> JSIO String) x

fsend_res : Ptr -> String -> JSIO ()
fsend_res x val = jscall "%0[1].send(%1)" (Ptr -> String -> JSIO ()) x val

install_service : Ptr -> (String, String -> JSIO String) -> JSIO ()
install_service ctrl (name, f) =
  do
    finstall_service ctrl name nf
  where
    nf x = do
            inp <- fget_serv_in x
            res <- f inp
            fsend_res x res


export
install_services : List (String, String -> JSIO String) -> JSIO ()
install_services x = do
  foxx <- require "org/arangodb/foxx"
  ctrl <- mkController foxx
  traverse  (install_service ctrl) x
  return ()
