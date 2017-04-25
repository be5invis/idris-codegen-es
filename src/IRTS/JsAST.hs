{-# LANGUAGE DeriveDataTypeable, OverloadedStrings #-}

module IRTS.JsAST( JsAST(..)
                 , jsAst2Text
                 , js_aux_defs
                 ) where

import Data.Text (Text)
import qualified Data.Text as T
import Data.Data

data JsAST = JsEmpty
           | JsNull
           | JsThis
           | JsLambda [Text] JsAST
           | JsFun Text [Text] JsAST
           | JsCurryFun Text [Text] JsAST
           | JsCurryFunExp [Text] JsAST
           | JsReturn JsAST
           | JsApp Text [JsAST]
           | JsAppE JsAST [JsAST]
           | JsCurryApp JsAST [JsAST]
           | JsPart JsAST Text
           | JsMethod JsAST Text [JsAST]
           | JsVar Text
           | JsSeq JsAST JsAST
           | JsDecVar Text JsAST
           | JsSetVar Text JsAST
           | JsSetA JsAST JsAST
           | JsArrayProj JsAST JsAST
           | JsObj [(Text, JsAST)]
           | JsProp JsAST Text
           | JsInt Int
           | JsInteger Integer
           | JsDouble Double
           | JsStr Text
           | JsArray [JsAST]
           | JsIf JsAST JsAST (Maybe JsAST)
           | JsSwitchCase JsAST [(JsAST, JsAST)] (Maybe JsAST)
           | JsError JsAST
           | JsErrorExp JsAST
           | JsBinOp Text JsAST JsAST
           | JsForeign Text [JsAST]
           | JsB2I JsAST
           | JsWhileTrue JsAST
           | JsContinue
           | JsBreak
           | JsComment Text
           | JsForce JsAST
           | JsLazy JsAST
            deriving (Show, Eq, Data, Typeable)


indent :: Text -> Text
indent x =
  let l  = T.lines x
      il = map (\y -> T.replicate 3 " " `T.append` y) l
  in T.unlines il

curryDef :: [Text] -> JsAST -> Text
curryDef [] body =
  jsAst2Text body
curryDef (x:xs) body =
  T.concat [ "function", "(", x, "){\n"
           , indent $ T.concat ["return ", curryDef xs body]
           , "}\n"
           ]


jsAst2Text :: JsAST -> Text
jsAst2Text JsEmpty = ""
jsAst2Text JsNull = "null"
jsAst2Text JsThis = "this"
jsAst2Text (JsLambda args body) =
  T.concat [ "(function", "(", T.intercalate ", " args , "){\n"
           , indent $ jsAst2Text body
           , "})"
           ]
jsAst2Text (JsFun name args body) =
  T.concat [ "function ", name, "(", T.intercalate ", " args , "){\n"
           , indent $ jsAst2Text body
           , "}\n"
           ]
jsAst2Text (JsCurryFunExp args body) = curryDef args body
jsAst2Text (JsCurryFun name args body) =
  T.concat [ "var ", name, " = \n"
           , indent $ T.concat [ "(function(){\n"
                               , indent $ T.concat ["return ", curryDef args body]
                               , "})()"
                               ]
           ]
{-  T.concat [ "function ", name, "(){\n"
           , indent $ jsAst2Text body
           , "}\n"
           ]
jsAst2Text (JsCurryFun name (x:xs) body) =
  T.concat [ "function ", name, "(",x,"){\n"
           , indent $ curryDef xs body
           , "}\n"
           ]-}
jsAst2Text (JsReturn x) = T.concat [ "return ", jsAst2Text x]
jsAst2Text (JsApp fn args) = T.concat [fn, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsAppE fn args) = T.concat [jsAst2Text fn, "(", T.intercalate ", " $ map jsAst2Text args, ")"]
jsAst2Text (JsCurryApp fn []) = jsAst2Text fn
jsAst2Text (JsCurryApp fn args) = T.concat [jsAst2Text fn, "(", T.intercalate ")(" $ map jsAst2Text args, ")"]
jsAst2Text (JsMethod obj name args) =
  T.concat [ jsAst2Text obj
           , "."
           , name, "("
           , T.intercalate ", " $ map jsAst2Text args
           , ")"
           ]
jsAst2Text (JsPart obj name) =
  T.concat [ jsAst2Text obj
           , "["
           , T.pack (show name)
           , "]"
           ]
jsAst2Text (JsVar x) = x
jsAst2Text (JsSeq JsEmpty y) = jsAst2Text y
jsAst2Text (JsSeq x JsEmpty) = jsAst2Text x
jsAst2Text (JsSeq x y) = T.concat [jsAst2Text x, ";\n", jsAst2Text y]
jsAst2Text (JsDecVar name exp) = T.concat [ "var ", name, " = ", jsAst2Text exp]
jsAst2Text (JsSetVar name exp) = T.concat [ name, " = ", jsAst2Text exp]
jsAst2Text (JsSetA name exp) = T.concat [ jsAst2Text name, " = ", jsAst2Text exp]
jsAst2Text (JsObj props) = T.concat [ "({"
                                    , T.intercalate ", " 
                                         (map (\(name, val) -> T.concat [name, ": ", jsAst2Text val]) 
                                              props)
                                    , "})"]
jsAst2Text (JsProp object name) = T.concat [ jsAst2Text object, ".", name]
jsAst2Text (JsArrayProj i exp) = T.concat [ jsAst2Text exp, "[", jsAst2Text i, "]"]
jsAst2Text (JsInt i) = T.pack $ show i
jsAst2Text (JsDouble d) = T.pack $ show d
jsAst2Text (JsInteger i) = T.pack $ show i
jsAst2Text (JsStr s) = T.pack $ show s
jsAst2Text (JsArray l) = T.concat [ "[", T.intercalate ", " (map jsAst2Text l), "]"]
jsAst2Text (JsIf cond conseq (Just alt@(JsIf _ _ _))) = T.concat [
  "if(", jsAst2Text cond, ") {\n",
    indent $ jsAst2Text conseq,
  "} else ",
    jsAst2Text alt]
jsAst2Text (JsIf cond conseq (Just alt)) = T.concat [
  "if(", jsAst2Text cond, ") {\n",
    indent $ jsAst2Text conseq,
  "} else {\n",
    indent $ jsAst2Text alt,
  "}\n"]
jsAst2Text (JsIf cond conseq Nothing) = T.concat [
  "if(", jsAst2Text cond, ") {\n",
    indent $ jsAst2Text conseq,
  "}\n"]
jsAst2Text (JsSwitchCase exp l d) =
  T.concat [ "switch(", jsAst2Text exp, "){\n"
           , indent $ T.concat $ map case2Text l
           , indent $ default2Text d
           , "}\n"
           ]
jsAst2Text (JsError t) =
  T.concat ["throw new Error(  ", jsAst2Text t, ")"]
jsAst2Text (JsErrorExp t) =
  T.concat ["js_idris_throw2(new Error(  ", jsAst2Text t, "))"]
jsAst2Text (JsBinOp op a1 a2) =
  T.concat ["(", jsAst2Text a1," ", op, " ",jsAst2Text a2, ")"]
jsAst2Text (JsForeign code args) =
  let args_repl c i [] = c
      args_repl c i (t:r) = args_repl (T.replace ("%" `T.append` T.pack (show i)) t c) (i+1) r
  in T.concat ["(", args_repl code 0 (map jsAst2Text args), ")"]
jsAst2Text (JsB2I x) = jsAst2Text $ JsBinOp "+" x (JsInt 0)
jsAst2Text (JsWhileTrue x) =
  T.concat [ "while(true){\n"
           , indent $ jsAst2Text x
           , "}\n"
           ]
jsAst2Text JsContinue =
  "continue"
jsAst2Text JsBreak =
  "break"
jsAst2Text (JsComment c)=
  T.concat ["/*",c,"*/"]
jsAst2Text (JsLazy e) =
  T.concat [ "{js_idris_lazy_calc:function(){"
           , indent $ jsAst2Text e
           , "}}"
           ]
jsAst2Text (JsForce e) =
  T.concat ["js_idris_force(", jsAst2Text e, ")"]



case2Text :: (JsAST, JsAST) -> Text
case2Text (x,y) =
  T.concat [ "case ", jsAst2Text x, ":\n"
           , indent $ T.concat [ jsAst2Text y, ";\nbreak;\n"]
           ]

throw2 = T.concat [ "var js_idris_throw2 = function (x){\n"
                  , " throw x;\n"
                  , "}\n\n"
                  ]

force  = T.concat [ "var js_idris_force = function (x){\n"
                  , " if(x.js_idris_lazy_calc === undefined){\n"
                  , "  return x\n"
                  , " }else{\n"
                  , "  if(x.js_idris_lazy_val === undefined){\n"
                  , "   x.js_idris_lazy_val = x.js_idris_lazy_calc()\n"
                  , "  }"
                  , "  return x.js_idris_lazy_val"
                  , "}"
                  , "}\n\n"
                  ]

js_aux_defs = T.concat [throw2, force]

default2Text :: Maybe JsAST -> Text
default2Text Nothing = ""
default2Text (Just z) =
  T.concat [ "default:\n"
           , indent $ T.concat [ jsAst2Text z, ";\nbreak;\n"]
           ]
