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



codegenJs :: CodeGenerator
codegenJs ci = do 
  let out = T.intercalate "\n" $ map doCodegen (simpleDecls ci)
  TIO.writeFile (outputFile ci) $ T.concat [ out, "\n"
                                           , start, "\n"
                                           , "\n\n"
                                           ]
                      
start = jsName (sMN 0 "runMain") `T.append` "();"

helpers = T.concat [ errCode, "\n" 
                   , mkStr, "\n"
                   , doAppend, "\n"
                   ]


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
cgBody ret (SApp _ f args) = 
  ret $ JsApp (jsName f) (map cgVar args)
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
  let scrvar = cgVar e 
      scr    = if any conCase alts then JsArrayProj (JsInt 0)  scrvar else scrvar 
  in JsSwitchCase scr (map (cgAlt ret scrvar) alts)  
  where conCase (SConCase _ _ _ _ _) = True
        conCase _ = False
cgBody ret (SConst c) = ret $ cgConst c
cgBody ret (SOp op args) = ret $ cgOp op (map cgVar args)
cgBody ret SNothing = ret $ JsInt 0
cgBody ret (SError x) = ret $ JsError $ T.pack $ x
cgBody ret x = error $ "Instruction " ++ show x ++ " not compilable yet"

cgAlt :: (JsAST -> JsAST) -> JsAST -> SAlt -> (JsAST, JsAST)
cgAlt ret scrvar (SConstCase t exp) = 
  (cgConst t, cgBody ret exp)
cgAlt ret scrvar (SDefaultCase exp) = 
  (JsVar "default", cgBody ret exp)
cgAlt ret scrvar (SConCase lv t n args exp) =
  (JsInt t, JsSeq (project 1 lv args) $ cgBody ret exp)
   where project i v [] = JsEmpty
         project i v (n : ns) = JsSeq (JsDecVar (loc v) (JsArrayProj (JsInt i) scrvar) ) $ project (i + 1) (v + 1) ns

cgVar :: LVar -> JsAST
cgVar (Loc i) = JsVar $ loc i 
cgVar (Glob n) = JsVar $ jsName n

cgConst :: Const -> JsAST
cgConst (I i) = JsInt i
--cgConst (Ch i) = show (ord i) -- Treat Char as ints, because PHP treats them as Strings...
--cgConst (BI i) = show i
cgConst (Str s) = JsStr $ T.pack s
--cgConst TheWorld = "0"
--cgConst x | isTypeConst x = "0"
cgConst x = error $ "Constant " ++ show x ++ " not compilable yet"

cgOp :: PrimFn -> [JsAST] -> JsAST
cgOp (LPlus (ATInt _)) [l, r] =
  JsPlus l r
{-cgOp (LMinus (ATInt _)) [l, r] 
     = "(" ++ l ++ " - " ++ r ++ ")"
cgOp (LTimes (ATInt _)) [l, r] 
     = "(" ++ l ++ " * " ++ r ++ ")"
cgOp (LEq (ATInt _)) [l, r] 
     = "(" ++ l ++ " == " ++ r ++ ")"
cgOp (LSLt (ATInt _)) [l, r] 
     = "(" ++ l ++ " < " ++ r ++ ")"
cgOp (LSLe (ATInt _)) [l, r] 
     = "(" ++ l ++ " <= " ++ r ++ ")"
cgOp (LSGt (ATInt _)) [l, r] 
     = "(" ++ l ++ " > " ++ r ++ ")"
cgOp (LSGe (ATInt _)) [l, r] 
     = "(" ++ l ++ " >= " ++ r ++ ")"
cgOp LStrEq [l,r] = "(" ++ l ++ " == " ++ r ++ ")"
cgOp LStrRev [x] = "strrev(" ++ x ++ ")"
cgOp LStrLen [x] = "strlen(utf8_decode(" ++ x ++ "))"
cgOp LStrHead [x] = "ord(" ++ x ++ "[0])"
cgOp LStrIndex [x, y] = "ord(" ++ x ++ "[" ++ y ++ "])"
cgOp LStrTail [x] = "substr(" ++ x ++ ", 1)"

cgOp (LIntStr _) [x] = "\"" ++ x ++ "\""
cgOp (LChInt _) [x] = x
cgOp (LIntCh _) [x] = x
cgOp (LSExt _ _) [x] = x
cgOp (LTrunc _ _) [x] = x
cgOp LWriteStr [_,str] = "idris_writeStr(" ++ str ++ ")"
cgOp LReadStr [_] = "idris_readStr()"
cgOp LStrConcat [l,r] = "idris_append(" ++ l ++ ", " ++ r ++ ")"
cgOp LStrCons [l,r] = "idris_append(chr(" ++ l ++ "), " ++ r ++ ")" -}
cgOp (LExternal n) _ = JsError $ T.pack $ "EXPERNAL OPERATOR " ++ show n ++ " NOT IMPLEMENTED!!!!"
cgOp op exps = error ("Operator " ++ show op ++ " not implemented")



