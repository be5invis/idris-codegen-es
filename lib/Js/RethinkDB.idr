module Js.RethinkDB

import Js.ASync
import public Js.Json
import Data.HVect
import Data.Vect
import Js.SimpleData

require : String -> JS_IO Ptr
require s = jscall "require(%0)" (String -> JS_IO Ptr) s

export
data Connection = MkConnection Ptr Ptr

toEitherErr : Ptr -> JS_IO (Either String Ptr)
toEitherErr x =
  do
    eq <- jscall "%0[0] ? 1 : 0" (Ptr -> JS_IO Int) x
    if eq == 1 then Left <$> jscall "%0[0] + ''" (Ptr -> JS_IO String) x
      else Right <$> jscall "%0[1]" (Ptr -> JS_IO Ptr) x

export
connect' : String -> Int -> JS_IO (Either String Connection)
connect' host port =
  do
    r <- require "rethinkdb"
    pc <- jscall
          "(function(){var res=null; %0.connect({'host': %1, 'port': %2},function(e,c){res = [e,c] } ); return res}())"
          (Ptr -> String -> Int -> JS_IO Ptr)
          r
          host
          port
    ec <- toEitherErr pc
    pure $ MkConnection r <$> ec

export
connect : String -> JS_IO Connection
connect host =
  do
    c <- connect' host 28015
    case c of
      Right r => pure r
      --Left e => error $ "Failded to connect to rethinkdb " ++ e


data Table : SDataObj -> Type where
  MkTable : String -> (a : SDataObj) -> Table a

export
data Query : SDataTy -> Type where
  BulkInsert : Table a -> List (iSDataObj a) -> Query (SObj [])



mkQuery : Ptr -> Query a -> JS_IO Ptr
mkQuery p (BulkInsert (MkTable name ptype) vals) =
  do
    v <- encodeJS (SList $ SObj ptype) vals
    jscall "%0.insert(%1)" (Ptr -> Ptr -> JS_IO Ptr) p v

export
runQuery : String -> Connection -> Query a -> JS_IO (Either String (iSDataTy a))
runQuery {a} database (MkConnection r c) q =
  do
    p <- jscall "%0.db(%1)" (Ptr -> String -> JS_IO Ptr) r database
    qq <- mkQuery p q
    v <- jscall "(function(){var res=null;%0.run(%1, function(a,b){res = [a,b]} ); return res}())" (Ptr -> Ptr -> JS_IO Ptr) qq c
    ev <- toEitherErr v
    case ev of
      Right z => decodeJS a z
