{-# LANGUAGE OverloadedStrings #-}

module IRTS.CodegenJs(codegenJs) where

import Control.DeepSeq
import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.Defunctionalise
import Idris.Core.TT

import IRTS.JsAST
import IRTS.DJsTransforms

import Data.Maybe (fromJust)
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.List (nub)
import System.Directory (doesFileExist)
import System.FilePath (combine)
import Control.Monad.Trans.State
import System.Environment

get_include :: FilePath -> IO Text
get_include p = TIO.readFile p

get_includes :: [FilePath] -> IO Text
get_includes l = do
  incs <- mapM get_include l
  return $ T.intercalate "\n\n" incs

genMaps :: [(Name, DDecl)] -> (Map Name Fun, Map Name Con)
genMaps x =
  (Map.fromList [(n, Fun n a e) | (_,DFun n a e) <- x ], Map.fromList [ (n,Con n i j) | (_, DConstructor n i j) <- x])

isYes :: Maybe String -> Bool
isYes (Just "Y") = True
isYes (Just "y") = True
isYes _ = False


codegenJs :: CodeGenerator
codegenJs ci =
  do
    optim <- isYes <$> lookupEnv "IDRISJS_OPTIM"
    debug <- isYes <$> lookupEnv "IDRISJS_DEBUG"
    if optim then putStrLn "compiling width idris-js optimizations" else putStrLn "compiling widthout idris-js optimizations"
    let decls = defunDecls ci
    let (funMap', conMap) = genMaps decls
    let funMap = inlineCons funMap' conMap
    let used = removeUnused funMap [sMN 0 "runMain"]
    used `deepseq` if debug then putStrLn $ "Finished removing unused" else pure ()
    inlined <- if optim then inline debug used else pure used
    inlined `deepseq` if debug then putStrLn $ "Finished inlining" else pure ()
    let out = T.intercalate "\n" $ map (doCodegen conMap) (Map.toList inlined)
    out `deepseq` if debug then putStrLn $ "Finished generating code" else pure ()
    includes <- get_includes $ includes ci
    TIO.writeFile (outputFile ci) $ T.concat [ "(function(){\n\n"
                                             , "\"use strict\";\n\n"
                                             , includes
                                             , out, "\n"
                                             , start, "\n"
                                             , "\n\n"
                                             , "\n}())"
                                             ]

throw2 = T.concat [ "var throw2 = function (x){\n"
                  , " throw x;\n"
                  , "}\n\n"
                  ]

start = T.concat [throw2,"\n\n", jsName (sMN 0 "runMain"), "();"]


jsName :: Name -> Text
jsName n = T.pack $ "idris_" ++ concatMap jschar (showCG n)
  where jschar x | isAlpha x || isDigit x = [x]
                  | otherwise = "_" ++ show (fromEnum x) ++ "_"


doCodegen :: Map Name Con -> (Name, Fun) -> Text
doCodegen decls (n, Fun _ args def) =
  jsAst2Text $ cgFun decls n args def

seqJs :: [JsAST] -> JsAST
seqJs [] = JsEmpty
seqJs (x:xs) = JsSeq x (seqJs xs)

data CGBodyState = CGBodyState { constructors :: Map Name Con
                               , lastIntName :: Int
                               , currentFnNameAndArgs :: (Text, [Text])
                               , isTailRec :: Bool
                               }

getNewCGName :: State CGBodyState Text
getNewCGName =
  do
    st <- get
    let v = lastIntName st + 1
    put $ st {lastIntName = v}
    return $ T.pack $ "cgIdris_" ++ show v

getConsId :: Name -> State CGBodyState Int
getConsId n =
    do
      st <- get
      case Map.lookup n (constructors st) of
        Just (Con _ conId _) -> pure conId
        _ -> error $ "ups " ++ showCG n


data BodyResTarget = ReturnBT
                   | DecVarBT Text
                   | SetVarBT Text
                   | GetExpBT

cgFun :: Map Name Con -> Name -> [Name] -> DExp -> JsAST
cgFun decls n args def =
  let
      fnName = jsName n
      argNames = map jsName args
      ((decs, res),st) = runState
                          (cgBody ReturnBT def)
                          (CGBodyState { constructors=decls
                                       , lastIntName = 0
                                       , currentFnNameAndArgs = (fnName, argNames)
                                       , isTailRec = False
                                       }
                          )
      body = if isTailRec st then JsWhileTrue $ (seqJs decs) `JsSeq` res `JsSeq` JsBreak
                else JsSeq (seqJs decs) res
  in JsFun fnName argNames $ body

getSwitchJs :: JsAST -> [DAlt] -> JsAST
getSwitchJs x alts =
  if any conCase alts then JsArrayProj (JsInt 0) x
    else x
  where conCase (DConCase _ _ _ _) = True
        conCase _ = False

addRT :: BodyResTarget -> JsAST -> JsAST
addRT ReturnBT x = JsReturn x
addRT (DecVarBT n) x = JsDecVar n x
addRT (SetVarBT n) x = JsSetVar n x
addRT GetExpBT x = x

cgBody :: BodyResTarget -> DExp -> State CGBodyState ([JsAST], JsAST)
cgBody rt (DV (Glob n)) =
  pure $ ([], addRT rt $ JsVar $ jsName n)
cgBody rt (DApp _ f args) =
  do
    let fname = jsName f
    st <- get
    let (currFn, argN) = currentFnNameAndArgs st
    z <- mapM (cgBody GetExpBT) args
    let preDecs = concat $ map fst z
    case (fname == currFn, rt) of
      (True, ReturnBT) ->
        do
          put $ st {isTailRec = True}
          vars <- sequence $ map (\_->getNewCGName) argN
          let calcs = map (\(n,v) -> JsDecVar n v) (zip vars (map snd z))
          let calcsToArgs = map (\(n,v) -> JsSetVar n (JsVar v)) (zip argN vars)
          pure (preDecs ++ calcs ++ calcsToArgs,  JsContinue)
      _ ->
        pure $ (preDecs, addRT rt $ JsApp (jsName f) (map snd z))
cgBody rt (DLet n v sc) =
  do
    (d1, v1) <- cgBody (DecVarBT $ jsName n) v
    (d2, v2) <- cgBody rt sc
    pure $ ((d1 ++ v1 : d2), v2 )
cgBody rt (DUpdate n ex) =
    do
      (d1, v1) <- cgBody GetExpBT ex
      let nm = jsName n
      pure $ (d1 ++ [JsSetVar nm v1], addRT rt $ JsVar nm)
cgBody rt (DProj e i) =
  do
    (d, v) <- cgBody GetExpBT e
    pure $ (d, addRT rt $ JsArrayProj (JsInt $ i+1) $ v)
cgBody rt (DC _  conId n args) =
  do
    z <- mapM (cgBody GetExpBT) args
    pure $ (concat $ map fst z, addRT rt $ JsArray (JsInt conId : map snd z))
cgBody rt (DCase _ e alts) =
  cgBody rt (DChkCase e alts)
cgBody rt (DChkCase e alts) =
  do
    (d,v) <- cgBody GetExpBT e
    resName <- getNewCGName
    swName <- getNewCGName
    (altsJs,def) <- cgAlts rt resName (JsVar swName) alts
    let decSw = JsDecVar swName v
    let sw = JsSwitchCase (getSwitchJs (JsVar swName) alts) altsJs def
    case rt of
      ReturnBT ->
        pure (d ++ [decSw], sw)
      (DecVarBT nvar) ->
        pure (d ++ [decSw, JsDecVar nvar JsNull], sw)
      (SetVarBT nvar) ->
        pure (d ++ [decSw], sw)
      GetExpBT ->
        pure (d ++ [decSw, JsDecVar resName JsNull, sw], JsVar resName)
cgBody rt (DConst c) = pure ([], (addRT rt) $ cgConst c)
cgBody rt (DOp op args) =
  do
    z <- mapM (cgBody GetExpBT) args
    pure $ (concat $ map fst z, addRT rt $ cgOp op (map snd z))
cgBody rt DNothing = pure ([], addRT rt JsNull)
cgBody rt (DError x) = pure ([JsError $ JsStr $ T.pack $ x], addRT rt JsNull)
cgBody rt x@(DForeign dres (FStr code) args ) =
  do
    z <- mapM (cgBody GetExpBT) (map snd args)
    let jsArgs = map cgForeignArg (zip (map fst args) (map snd z))
    pure $ (concat $ map fst z, addRT rt $ cgForeignRes dres $ JsForeign (T.pack code) jsArgs)
cgBody _ x = error $ "Instruction " ++ show x ++ " not compilable yet"

conCaseToProjs :: Int -> JsAST -> [Name] -> JsAST
conCaseToProjs _ _ [] = JsEmpty
conCaseToProjs i v (x:xs) = JsSeq (JsDecVar (jsName x) $ JsArrayProj (JsInt i) v) $ conCaseToProjs (i+1) v xs


altsRT :: Text -> BodyResTarget -> BodyResTarget
altsRT rn ReturnBT = ReturnBT
altsRT rn (DecVarBT n) = SetVarBT n
altsRT rn (SetVarBT n) = SetVarBT n
altsRT rn GetExpBT = SetVarBT rn

cgAlts :: BodyResTarget -> Text -> JsAST -> [DAlt] -> State CGBodyState ([(JsAST, JsAST)], Maybe JsAST)
cgAlts rt resName scrvar ((DConstCase t exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    (ar, def) <- cgAlts rt resName scrvar r
    pure ((cgConst t, JsSeq (seqJs d) v) : ar, def)
cgAlts rt resName scrvar ((DDefaultCase exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    pure ([], Just $ JsSeq (seqJs d) v)
cgAlts rt resName scrvar ((DConCase _ n args exp):r) =
  do
    (d, v) <- cgBody (altsRT resName rt) exp
    (ar, def) <- cgAlts rt resName scrvar r
    conId <- getConsId n
    let branchBody = JsSeq (conCaseToProjs 1 scrvar args) $ JsSeq (seqJs d) v
    pure ((JsInt conId, branchBody) : ar, def)
cgAlts _ _ _ [] =
  pure ([],Nothing)

apply_name = jsName $ sMN 0 "APPLY"
eval_name = jsName $ sMN 0 "EVAL"


cgForeignArg :: (FDesc, JsAST) -> JsAST
cgForeignArg (FApp (UN "JS_IntT") _, v) = v
cgForeignArg (FCon (UN "JS_Str"), v) = v
cgForeignArg (FCon (UN "JS_Ptr"), v) = v
cgForeignArg (FCon (UN "JS_Unit"), v) = v
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnBase") [_,b]]], f) =
  JsAFun ["x"] $ JsReturn $ cgForeignRes b $ JsApp apply_name [f, cgForeignArg (a, JsVar "x")]
cgForeignArg (FApp (UN "JS_FnT") [_,FApp (UN "JS_Fn") [_,_, a, FApp (UN "JS_FnIO") [_,_, b]]], f) =
  JsAFun ["x"] $ JsReturn $ cgForeignRes b $ evalJSIO $ JsApp apply_name [f, cgForeignArg (a, JsVar "x")]
cgForeignArg (desc, _) = error $ "Foreign arg type " ++ show desc ++ " not supported yet."

evalJSIO :: JsAST -> JsAST
evalJSIO x =
  JsAppIfDef eval_name (JsApp apply_name [x, JsInt 0])

cgForeignRes :: FDesc -> JsAST -> JsAST
cgForeignRes (FApp (UN "JS_IntT") _) x = x
cgForeignRes (FCon (UN "JS_Unit")) x = x
cgForeignRes (FCon (UN "JS_Str")) x = x
cgForeignRes (FCon (UN "JS_Ptr")) x =  x
cgForeignRes (FCon (UN "JS_Float")) x = x
cgForeignRes desc val =  error $ "Foreign return type " ++ show desc ++ " not supported yet."

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
cgOp (LEq _) [l, r] = JsB2I $ JsBinOp "==" l r
cgOp (LSLt _) [l, r] = JsB2I $ JsBinOp "<" l r
cgOp (LSLe _) [l, r] = JsB2I $ JsBinOp "<=" l r
cgOp (LSGt _) [l, r] = JsB2I $ JsBinOp ">" l r
cgOp (LSGe _) [l, r] = JsB2I $ JsBinOp ">=" l r
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
cgOp LCrash [l] = JsErrorExp l
cgOp op exps = error ("Operator " ++ show (op, exps) ++ " not implemented")
