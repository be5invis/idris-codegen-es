{-# LANGUAGE OverloadedStrings #-}

module IRTS.JsAST( JsAST(..)
                 , jsAst2Text
                 ) where

import Data.Text (Text)
import qualified Data.Text as T

data JsAST = JsEmpty
           | JsFun Text [Text] JsAST
           | JsReturn JsAST
           | JsApp Text [JsAST]
           | JsMethod JsAST Text [JsAST]
           | JsVar Text
           | JsSeq JsAST JsAST
           | JsDecVar Text JsAST
           | JsArrayProj JsAST JsAST
           | JsInt Int
           | JsInteger Integer
           | JsStr Text
           | JsArray [JsAST]
           | JsSwitchCase JsAST [(JsAST, JsAST)] (Maybe JsAST)
           | JsError Text
           | JsBinOp Text JsAST JsAST
           | JsForeign Text [JsAST]
           | JsAFun [Text] JsAST
            deriving (Show, Eq)


indent :: Text -> Text
indent x = 
  let l  = T.lines x
      il = map (\y -> T.replicate 3 " " `T.append` y) l
  in T.unlines il

jsAst2Text :: JsAST -> Text
jsAst2Text JsEmpty = ""
jsAst2Text (JsFun name args body) =
  T.concat [ "function ", name, "(", T.intercalate ", " args , "){\n"
           , indent $ jsAst2Text body
           , "}\n"
           ]
jsAst2Text (JsReturn x) = T.concat [ "return ", jsAst2Text x]
jsAst2Text (JsApp name args) = T.concat [name, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsMethod obj name args) = T.concat [jsAst2Text obj, ".", name, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsVar x) = x
jsAst2Text (JsSeq x y) = T.concat [jsAst2Text x, ";\n", jsAst2Text y]
jsAst2Text (JsDecVar name exp) = T.concat [ "var ", name, " = ", jsAst2Text exp]
jsAst2Text (JsArrayProj i exp) = T.concat [ jsAst2Text exp, "[", jsAst2Text i, "]"]
jsAst2Text (JsInt i) = T.pack $ show i
jsAst2Text (JsInteger i) = T.pack $ show i
jsAst2Text (JsStr s) = T.pack $ show s
jsAst2Text (JsArray l) = T.concat [ "[", T.intercalate ", " (map jsAst2Text l), "]"]
jsAst2Text (JsSwitchCase exp l d) =
  T.concat [ "switch(", jsAst2Text exp, "){\n"
           , indent $ T.concat $ map case2Text l
           , indent $ default2Text d
           , "}\n"
           ]
jsAst2Text (JsError t) = 
  T.concat ["throw new Error(  ", T.pack $ show t, ")"]
jsAst2Text (JsBinOp op a1 a2) =
  T.concat ["(", jsAst2Text a1," ", op, " ",jsAst2Text a2, ")"]
jsAst2Text (JsForeign code args) =
  let args_repl c i [] = c
      args_repl c i (t:r) = args_repl (T.replace ("%" `T.append` T.pack (show i)) t c) (i+1) r
  in args_repl code 0 (map jsAst2Text args)
jsAst2Text (JsAFun l body) = T.concat ["(function(", T.intercalate ", " l, "){", jsAst2Text body, "})"]


case2Text :: (JsAST, JsAST) -> Text
case2Text (x,y) = 
  T.concat [ "case ", jsAst2Text x, ":\n"
           , indent $ T.concat [ jsAst2Text y, ";\nbreak;\n"]
           ]

default2Text :: Maybe JsAST -> Text
default2Text Nothing = ""
default2Text (Just z) = 
  T.concat [ "default:\n"
           , indent $ T.concat [ jsAst2Text z, ";\nbreak;\n"]
           ]


