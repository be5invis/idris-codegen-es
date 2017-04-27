{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenEs.Specialize
  ( SCtor
  , STest
  , SProj
  , specialCased
  ) where

import Data.Char
import Data.List
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import IRTS.CodegenEs.JsAST
import Idris.Core.TT

-- special-cased constructors
type SCtor = [JsAST] -> JsAST

type STest = JsAST -> JsAST

type SProj = JsAST -> Int -> JsAST

constructorOptimizeDB :: Map.Map Name (SCtor, STest, SProj)
constructorOptimizeDB =
  Map.fromList
    [ item "Prelude.Bool" "True" (const $ JsBool True) id cantProj
    , item "Prelude.Bool" "False" (const $ JsBool False) falseTest cantProj
    -- , item "Prelude.List" "::" cons fillList uncons
    -- , item "Prelude.List" "Nil" nil emptyList cantProj
    -- , item "Prelude.Maybe" "Just" (\[x] -> x) notNoneTest justProj
    -- , item "Prelude.Maybe" "Nothing" (const $ JsUndefined) noneTest cantProj
    ]
  where
    -- constructors
    nil = const $ JsArray []
    cons [h, t] = JsMethod (JsArray [h]) "concat" [t]
    -- tests
    falseTest e = JsUniOp (T.pack "!") e
    emptyList e = JsBinOp "===" (JsProp e "length") (JsInt 0)
    fillList e = JsBinOp ">" (JsProp e "length") (JsInt 0)
    noneTest e = JsBinOp "===" e JsUndefined
    notNoneTest e = JsBinOp "!==" e JsUndefined
    -- projections
    justProj x n = x
    uncons x 1 = JsArrayProj (JsInt 0) x
    uncons x 2 = JsMethod x "slice" [JsInt 1]
    cantProj x j = error $ "This type should be projected"
    item :: String
         -> String
         -> SCtor
         -> STest
         -> SProj
         -> (Name, (SCtor, STest, SProj))
    item "" n ctor test match = (sUN n, (ctor, test, match))
    item ns n ctor test match =
      (sNS (sUN n) (reverse $ split '.' ns), (ctor, test, match))
    split :: Char -> String -> [String]
    split c "" = [""]
    split c (x:xs)
      | c == x = "" : split c xs
      | otherwise =
        let ~(h:t) = split c xs
        in ((x : h) : t)

specialCased :: Name -> Maybe (SCtor, STest, SProj)
specialCased n = Map.lookup n constructorOptimizeDB
