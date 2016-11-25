{-# LANGUAGE OverloadedStrings #-}

module IRTS.CodegenJs(codegenJs) where

import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Defunctionalise
import Idris.Core.TT
import IRTS.Simplified

import IRTS.JsAST

import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Data.List (nub)
import System.Directory (doesFileExist)
import System.FilePath (combine)


used_functions_exp :: SExp -> [Name]
used_functions_exp x =
  nub $ used x
  where
    used (SV _) = []
    used (SApp _ n _) = [n]
    used (SLet _ a b) = used a ++ used b
    used (SUpdate _ a) = used a
    used (SCon _ _ _ _) = []
    used (SCase _ _ a) = concatMap used_alt a
    used (SChkCase _ a) = concatMap used_alt a
    used (SProj _ _) = []
    used (SConst _) = []
    used (SForeign _ _ _) = []
    used (SOp _ _) = []
    used SNothing = []
    used (SError _) = []
--    used x = error $ "Instruction " ++ show x ++ " missing clause in used"

    used_alt (SConCase _ _ _ _ a) = used a
    used_alt (SConstCase _ a) = used a
    used_alt (SDefaultCase a) = used a


used_functions :: Map Name SDecl -> [Name] -> Set Name
used_functions _ [] = Set.empty
used_functions alldefs (next_name:rest) =
  let new_names = case Map.lookup next_name alldefs of
                    Just (SFun _ _ _ e) -> filter (\x -> Map.member x alldefs) $ used_functions_exp e
                    _                   -> []
  in Set.insert next_name $ used_functions (Map.delete next_name alldefs) (rest ++ new_names)


get_include :: FilePath -> IO Text
get_include p = TIO.readFile p

get_includes :: [FilePath] -> IO Text
get_includes l = do
  incs <- mapM get_include l
  return $ T.intercalate "\n\n" incs

codegenJs :: CodeGenerator
codegenJs ci = do
  let sdecls         = simpleDecls ci
      used           = used_functions (Map.fromList sdecls) [sMN 0 "runMain"]
      filtered_decls = filter (\(k,v) -> Set.member k used ) sdecls
      out            = T.intercalate "\n" $ map doCodegen filtered_decls
  includes <- get_includes $ includes ci
  TIO.writeFile (outputFile ci) $ T.concat [ "(function(){\n\n"
                                           , "\"use strict\";\n\n"
                                           , includes
                                           , out, "\n"
                                           , start, "\n"
                                           , "\n\n"
                                           , "\n}())"
                                           ]

trampoline = T.concat [ "var idris_trampoline = function(val){\n"
                      , "   var res = val;\n"
                      , "   while(res && res.call_trampoline_idrisjs){\n"
                      , "     res = res.call_trampoline_idrisjs.apply(this, res.args);\n"
                      , "   }\n"
                      , "   return res\n"
                      , "}\n"
                      ]

throw2 = T.concat [ "var throw2 = function (x){\n"
                  , " throw x;\n"
                  , "}\n\n"
                  ]

start = T.concat [throw2,trampoline,"\n\nidris_trampoline", "(", jsName (sMN 0 "runMain"), "());"]


jsName :: Name -> Text
jsName n = T.pack $ "idris_" ++ concatMap jschar (showCG n)
  where jschar x | isAlpha x || isDigit x = [x]
                  | otherwise = "_" ++ show (fromEnum x) ++ "_"


loc :: Int -> Text
loc i = T.pack $ "loc" ++ show i

doCodegen :: (Name, SDecl) -> Text
doCodegen (n, SFun _ args i def) = jsAst2Text $ cgFun n args def

cgFun :: Name -> [Name] -> SExp -> JsAST
cgFun n args def =
  JsFun (jsName n) (map (loc . fst) (zip [0..] args)) (cgBody doRet def)
  where doRet :: JsAST -> JsAST
        doRet x = JsReturn x


cgBody :: (JsAST -> JsAST) -> SExp -> JsAST
cgBody ret (SV (Glob n)) =
  ret $ JsApp (jsName n) []
cgBody ret (SV (Loc i)) =
  ret $ JsVar $ loc i
cgBody ret (SApp False f args) =
  ret $ JsApp (jsName f) (map cgVar args)
cgBody ret (SApp True f args) =
  ret $ JsAppTrampoline (jsName f) (map cgVar args)
cgBody ret (SLet (Loc i) v sc) =
  JsSeq
    (cgBody (\x -> JsDecVar (loc i) x) v)
    (cgBody ret sc)
cgBody ret (SUpdate n e) =
  cgBody ret e
cgBody ret (SProj e i) =
  ret $ JsArrayProj (JsInt $ i+1) $ cgVar e
cgBody ret (SCon _ t n args) =
  ret $ JsArray (JsInt t : (map cgVar args))
cgBody ret (SCase _ e alts) =
  cgBody ret (SChkCase e alts)
cgBody ret (SChkCase e alts) =
  let scrvar     = cgVar e
      scr        = if any conCase alts then JsArrayProj (JsInt 0)  scrvar else scrvar
      (as, de) = cgAlts ret scrvar alts
  in JsSwitchCase scr as de
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False
cgBody ret (SConst c) = ret $ cgConst c
cgBody ret (SOp op args) = ret $ cgOp op (map cgVar args)
cgBody ret SNothing = ret $ JsNull
cgBody ret (SError x) = JsError $ T.pack $ x
cgBody ret x@(SForeign dres (FStr code) args ) =
  cgForeignRes ret dres $ JsForeign (T.pack code) (map cgForeignArg (map (\(x,y) -> (x, cgVar y)) args))
cgBody ret x = error $ "Instruction " ++ show x ++ " not compilable yet"

cgAlts :: (JsAST -> JsAST) -> JsAST -> [SAlt] -> ([(JsAST, JsAST)], Maybe JsAST)
cgAlts ret scrvar ((SConstCase t exp):r) =
  let (ar, d) = cgAlts ret scrvar r
  in ((cgConst t, cgBody ret exp):ar, d)
cgAlts ret scrvar ((SConCase lv t n args exp):r) =
  let (ar, d) = cgAlts ret scrvar r
  in ((JsInt t, JsSeq (project 1 lv args) $ cgBody ret exp):ar, d)
   where project i v [] = JsEmpty
         project i v (n : ns) = JsSeq (JsDecVar (loc v) (JsArrayProj (JsInt i) scrvar) ) $ project (i + 1) (v + 1) ns
cgAlts ret scrvar ((SDefaultCase exp):r) =
  ([], Just $ cgBody ret exp)
cgAlts _ _ [] = ([],Nothing)

apply_name = jsName $ sMN 0 "APPLY"
eval_name = jsName $ sMN 0 "EVAL"


cgForeignArg :: (FDesc, JsAST) -> JsAST
cgForeignArg (FApp (UN "JS_IntT") _, v) = v
cgForeignArg (FCon (UN "JS_Str"), v) = v
cgForeignArg (FCon (UN "JS_Ptr"), v) = v
cgForeignArg (FCon (UN "JS_Unit"), v) = v
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnBase") [_,b]]], f) =
  JsAFun ["x"] $ cgForeignRes JsReturn b $ JsApp apply_name [f, cgForeignArg (a, JsVar "x")]
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnIO") [_,_, b]]], f) =
  JsAFun ["x"] $ cgForeignRes JsReturn b $ evalJSIO $ JsApp apply_name [f, cgForeignArg (a, JsVar "x")]
--cgForeignArg (FApp (UN "JsFunIO") [_, _, a, b], f) =
--  JsAFun ["x"] $ cgForeignRes JsReturn b $ evalJSIO $ JsApp apply_name [f, cgForeignArg (a, JsVar "x")]
cgForeignArg (desc, _) = error $ "Foreign arg type " ++ show desc ++ " not supported yet."

evalJSIO :: JsAST -> JsAST
evalJSIO x =
  JsAppIfDef eval_name (JsApp apply_name [x, JsInt 0])

cgForeignRes :: (JsAST -> JsAST) -> FDesc -> JsAST -> JsAST
cgForeignRes ret (FApp (UN "JS_IntT") _) x = ret x
cgForeignRes ret (FCon (UN "JS_Unit")) x = ret x
cgForeignRes ret (FCon (UN "C_Unit")) x = ret x
cgForeignRes ret (FCon (UN "JS_Str")) x = ret x
cgForeignRes ret (FCon (UN "JS_Ptr")) x = ret x
cgForeignRes ret (FCon (UN "JS_Float")) x = ret x
cgForeignRes ret desc val =  error $ "Foreign return type " ++ show desc ++ " not supported yet."

cgVar :: LVar -> JsAST
cgVar (Loc i) = JsVar $ loc i
cgVar (Glob n) = JsVar $ jsName n

cgConst :: Const -> JsAST
cgConst (I i) = JsInt i
cgConst (BI i) = JsInteger i
cgConst (Ch c) = JsInt $ ord c
cgConst (Str s) = JsStr $ T.pack s
cgConst (Fl f) = JsDouble f
cgConst (B8 x) = error "error B8"
cgConst (B16 x) = error "error B16"
cgConst (B32 x) = error "error B32"
cgConst (B64 x) = error "error B64"
cgConst x | isTypeConst x = JsInt 0
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [JsAST] -> JsAST
cgOp (LPlus _) [l, r] = JsBinOp "+" l r
cgOp (LMinus _) [l, r] = JsBinOp "-" l r
cgOp (LTimes _) [l, r] = JsBinOp "*" l r
cgOp (LEq (ATInt _)) [l, r] = JsB2I $ JsBinOp "==" l r
cgOp (LSLt (ATInt _)) [l, r] = JsB2I $ JsBinOp "<" l r
cgOp (LSLe (ATInt _)) [l, r] = JsB2I $ JsBinOp "<=" l r
cgOp (LSGt (ATInt _)) [l, r] = JsB2I $ JsBinOp ">" l r
cgOp (LSGe (ATInt _)) [l, r] = JsB2I $ JsBinOp ">=" l r
cgOp LStrEq [l,r] = JsB2I $ JsBinOp "==" l r
cgOp LStrLen [x] = JsForeign "%0.length" [x]
cgOp LStrHead [x] = JsMethod x "charCodeAt" [JsInt 0]
cgOp LStrIndex [x, y] = JsMethod x "charCodeAt" [y]
cgOp LStrTail [x] = JsMethod x "slice" [JsInt 1]
cgOp LStrLt [l, r] = JsB2I $ JsBinOp "<" l r
cgOp (LFloatStr) [x] = JsBinOp "+" x (JsStr "")
cgOp (LIntStr _) [x] = JsBinOp "+" x (JsStr "")
cgOp (LFloatInt _) [x] = JsApp "Math.trunc" [x]
cgOp (LStrInt _) [x] = JsBinOp "||" (JsApp "parseInt" [x]) (JsInt 0)
cgOp (LStrFloat) [x] = JsBinOp "||" (JsApp "parseFloat" [x]) (JsInt 0)
cgOp (LChInt _) [x] = x
cgOp (LIntCh _) [x] = x
cgOp (LSExt _ _) [x] = x
cgOp (LZExt _ _) [x] = x
cgOp (LIntFloat _) [x] = x
cgOp (LSDiv _) [x,y] = JsBinOp "/" x y
cgOp LWriteStr [_,str] = JsApp "console.log" [str]
cgOp LStrConcat [l,r] = JsBinOp "+" l r
cgOp LStrCons [l,r] = JsForeign "String.fromCharCode(%0) + %1" [l,r]
cgOp (LSRem (ATInt _)) [l,r] = JsBinOp "%" l r
cgOp op exps = error ("Operator " ++ show (op, exps) ++ " not implemented")
