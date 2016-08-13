module Js.RethinkDB

import Js.ASync
import public Js.Json
import public Js.SimpleData
import Js.Node

require : String -> JS_IO Ptr
require s = jscall "require(%0)" (String -> JS_IO Ptr) s

export
data Connection = MkConnection Ptr Ptr

export
connect' : String -> Int -> ASync Connection
connect' host port =
  do
    r <- liftJS_IO $ require "rethinkdb"
    c <- handleErr $ MkASync $ \proc =>
      jscall
        "%0.connect({'host': %1,'port': %2}, function(e,c){%3([e,c])}  ) "
        (Ptr -> String -> Int -> JsFn (Ptr -> JS_IO ()) -> JS_IO () )
        r
        host
        port
        (MkJsFn proc)
    pure $ MkConnection r c


export
connect : String -> ASync Connection
connect host = connect' host 28015

export
data Table : SDataObj -> Type where
  MkTable : String -> String -> (a : SDataObj) -> Table a

export
table : String -> String -> Table a
table {a} x y = MkTable x y a

public export
InsertInfo : SDataTy
InsertInfo = SObj []

export
data Query : SDataTy -> Type where
  Insert : Table a -> List (ISDataObj a) -> Query InsertInfo


mkQuery : Ptr -> Query a -> JS_IO Ptr
mkQuery p (Insert (MkTable database name ptype) vals) =
  do
    v <- encodeJS (SList $ SObj ptype) vals
    jscall "%2.db(%0).table(%1).insert(%3)" (String -> String -> Ptr -> Ptr -> JS_IO Ptr) database name p v


export
runQuery' : Connection -> Query a -> ASync (Either String (ISDataTy a))
runQuery' {a} (MkConnection r c) q =
  do
    qq <- liftJS_IO $ mkQuery r q
    decodeRes $ err2Either $ MkASync $ \proc =>
      jscall "%0.run(%1,function(e,c){%2([e,c])})"
        (Ptr -> Ptr -> JsFn (Ptr -> JS_IO ()) -> JS_IO () )
        qq
        c
        (MkJsFn proc)
  where
    decodeRes : ASync (Either String Ptr) -> ASync  (Either String (ISDataTy a))
    decodeRes x =
      case !x of
          Left e => pure $ Left e
          Right y => liftJS_IO $ decodeJS a y

export
runQuery : Connection -> Query a -> ASync (ISDataTy a)
runQuery conn q =
  do
    res <- runQuery' conn q
    case res of
      Right x => pure x
      Left e => error e

export
createTable : String -> Connection -> String -> ASync ()
createTable database (MkConnection r c) tableName =
    map (\_ => ()) $ handleErr $ MkASync $ \proc =>
      jscall
        "%0.db(%1).tableCreate(%2).run(%3, function(e,c){%4([e,c])}  ) "
        (Ptr -> String -> String -> Ptr -> JsFn (Ptr -> JS_IO ()) -> JS_IO () )
        r
        database
        tableName
        c
        (MkJsFn proc)

export
insert : Table a -> List (ISDataObj a) -> Query InsertInfo
insert = Insert

export
insert1 : Table a -> ISDataObj a -> Query InsertInfo
insert1 x y = Insert x [y]
