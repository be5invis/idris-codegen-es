{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenEs
  ( codegenJs
  ) where

import Control.DeepSeq
import IRTS.CodegenCommon
import IRTS.Lang
import IRTS.LangOpts
import Idris.Core.TT

import IRTS.CodegenEs.JsAST
import IRTS.CodegenEs.LangTransforms
import IRTS.CodegenEs.Specialize

import Control.Monad.Trans.State
import Data.Char
import Data.List (nub)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Maybe (fromJust)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Text.IO as TIO
import System.Directory (doesFileExist)
import System.Environment
import System.FilePath (combine)

import Data.Data
import Data.Generics.Uniplate.Data
import Data.List
import GHC.Generics (Generic)

get_include :: FilePath -> IO Text
get_include p = TIO.readFile p

get_includes :: [FilePath] -> IO Text
get_includes l = do
  incs <- mapM get_include l
  return $ T.intercalate "\n\n" incs

isYes :: Maybe String -> Bool
isYes (Just "Y") = True
isYes (Just "y") = True
isYes _ = False

type ArityMap = Map.Map Text Int

codegenJs :: CodeGenerator
codegenJs ci = do
  optim <- isYes <$> lookupEnv "IDRISJS_OPTIM"
  debug <- isYes <$> lookupEnv "IDRISJS_DEBUG"
  {-
  if optim
    then putStrLn "compiling with idris-js optimizations"
    else putStrLn "compiling without idris-js optimizations"
  -}
  let defs = addAlist (liftDecls ci) emptyContext -- Map.fromList $ liftDecls ci
  let used = used_decls defs [sMN 0 "runMain"] --removeUnused dcls dclsMap [sMN 0 "runMain"]
  used `deepseq`
    if debug
      then do
        putStrLn $ "Finished calculating used"
        writeFile (outputFile ci ++ ".LDecls") $
          (unlines $ intersperse "" $ map show used) ++ "\n\n\n"
      else pure ()
    --let inlined = if optim then inline used else used -- <- if optim then inline debug used else pure used
    --inlined `deepseq` if debug then putStrLn $ "Finished inlining" else pure ()
  let out = T.intercalate "\n" $ map (doCodegen defs) used
  out `deepseq`
    if debug
      then putStrLn $ "Finished generating code"
      else pure ()
  includes <- get_includes $ includes ci
  TIO.writeFile (outputFile ci) $
    T.concat
      [ "(function(){\n\n"
      , "\"use strict\";\n\n"
      , includes
      , "\n"
      , js_aux_defs
      , "\n"
      , out
      , "\n}())"
      ]

jsEscape :: String -> String
jsEscape = concatMap jschar
  where
    jschar x
      | isAlpha x || isDigit x = [x]
      | x == '_' = "__"
      | otherwise = "_" ++ show (fromEnum x) ++ "_"

showCGJS :: Name -> (String, String)
showCGJS (UN n) = ("u_", jsEscape $ T.unpack n)
showCGJS (NS n s) =
  ( "q_"
  , showSep "$" (map (jsEscape . T.unpack) (reverse s)) ++
    "$$" ++ (snd $ showCGJS n))
showCGJS (MN _ u)
  | u == txt "underscore" = ("", "_")
showCGJS (MN i s) = ("_", (jsEscape $ T.unpack s) ++ "$" ++ show i)
showCGJS n = ("x_", jsEscape $ showCG n)

jsName :: Name -> Text
jsName n =
  let (prefix, name) = showCGJS n
  in T.pack $ prefix ++ name

doCodegen :: LDefs -> LDecl -> Text
doCodegen defs (LFun _ n args def) = jsAst2Text $ cgFun defs n args def
doCodegen defs (LConstructor n i sz) = ""

seqJs :: [JsAST] -> JsAST
seqJs [] = JsEmpty
seqJs (x:xs) = JsSeq x (seqJs xs)

data CGBodyState = CGBodyState
  { defs :: LDefs
  , lastIntName :: Int
  , currentFnNameAndArgs :: (Text, [Text])
  , isTailRec :: Bool
  }

getNewCGName :: State CGBodyState Text
getNewCGName = do
  st <- get
  let v = lastIntName st + 1
  put $ st {lastIntName = v}
  return $ T.pack $ "cgIdris_" ++ show v

getConsId :: Name -> State CGBodyState (Int, Int)
getConsId n = do
  st <- get
  case lookupCtxtExact n (defs st) of
    Just (LConstructor _ conId arity) -> pure (conId, arity)
    _ -> error $ "ups " ++ (snd . showCGJS) n

data BodyResTarget
  = ReturnBT
  | DecVarBT Text
  | SetVarBT Text
  | GetExpBT

cgFun :: LDefs -> Name -> [Name] -> LExp -> JsAST
cgFun dfs n args def =
  let fnName = jsName n
      argNames = map jsName args
      ((decs, res), st) =
        runState
          (cgBody ReturnBT def)
          (CGBodyState
           { defs = dfs
           , lastIntName = 0
           , currentFnNameAndArgs = (fnName, argNames)
           , isTailRec = False
           })
      body =
        if isTailRec st
          then JsForever $ (seqJs decs) `JsSeq` res `JsSeq` JsBreak
          else JsSeq (seqJs decs) res
  in if (length argNames > 0)
       then JsFun fnName argNames body
       else JsDecVar fnName $ JsAppE (JsLambda [] body) []

addRT :: BodyResTarget -> JsAST -> JsAST
addRT ReturnBT x = JsReturn x
addRT (DecVarBT n) x = JsDecVar n x
addRT (SetVarBT n) x = JsSetVar n x
addRT GetExpBT x = x

cgBody :: BodyResTarget -> LExp -> State CGBodyState ([JsAST], JsAST)
cgBody rt (LV (Glob n)) = do
  st <- get
  case (lookupCtxtExact n (defs st)) of
    Just (LFun _ _ [a] d) -> pure $ ([], addRT rt $ JsVar $ jsName n)
    _ -> cgBody rt (LApp False (LV (Glob n)) []) -- recurry
cgBody rt (LApp _ (LV (Glob fn)) args) = do
  let fname = jsName fn
  st <- get
  let (currFn, argN) = currentFnNameAndArgs st
  z <- mapM (cgBody GetExpBT) args
  let preDecs = concat $ map fst z
  case (fname == currFn, rt) of
    (True, ReturnBT) -> do
      put $ st {isTailRec = True}
      vars <- sequence $ map (\_ -> getNewCGName) argN
      let calcs = map (\(n, v) -> JsDecVar n v) (zip vars (map snd z))
      let calcsToArgs = map (\(n, v) -> JsSetVar n (JsVar v)) (zip argN vars)
      pure (preDecs ++ calcs ++ calcsToArgs, JsContinue)
    _ -> pure $ (preDecs, addRT rt $ formApp (defs st) fn (map snd z))
cgBody rt (LForce (LLazyApp n args)) = cgBody rt (LApp False (LV (Glob n)) args)
cgBody rt (LLazyApp fn args) = do
  st <- get
  z <- mapM (cgBody GetExpBT) args
  let preDecs = concat $ map fst z
  let na = map (T.pack . ("$" ++) . show) $ take (length z) [1 ..]
  pure
    ( preDecs
    , JsAppE
        (JsLambda (na) $ JsReturn $ jsLazy $ formApp (defs st) fn (map JsVar na))
        (map snd z))
  -- (d, v) <- cgBody ReturnBT (LApp False (LV (Glob n)) args)
  -- pure ([], addRT rt $ JsLazy $ JsSeq (seqJs d) v)
cgBody rt (LForce e) = do
  (d, v) <- cgBody GetExpBT e
  pure (d, addRT rt $ JsForce v)
cgBody rt (LLet n v sc) = do
  (d1, v1) <- cgBody (DecVarBT $ jsName n) v
  (d2, v2) <- cgBody rt sc
  pure $ ((d1 ++ v1 : d2), v2)
cgBody rt (LProj e i) = do
  (d, v) <- cgBody GetExpBT e
  pure $ (d, addRT rt $ JsProp v (T.pack $ "$" ++ (show $ i + 1)))
cgBody rt (LCon _ conId n args) = do
  z <- mapM (cgBody GetExpBT) args
  con <- formCon n (map snd z)
  pure $ (concat $ map fst z, addRT rt con)
cgBody rt (LCase _ e alts) = do
  (d, v) <- cgBody GetExpBT e
  resName <- getNewCGName
  swName <- getNewCGName
  sw' <- cgIfTree rt resName (JsVar swName) alts
  let sw =
        case sw' of
          (Just x) -> x
          Nothing -> JsNull
  let decSw = JsDecVar swName v
  case rt of
    ReturnBT -> pure (d ++ [decSw], sw)
    (DecVarBT nvar) -> pure (d ++ [decSw, JsDecVar nvar JsNull], sw)
    (SetVarBT nvar) -> pure (d ++ [decSw], sw)
    GetExpBT -> pure (d ++ [decSw, JsDecVar resName JsNull, sw], JsVar resName)
cgBody rt (LConst c) = pure ([], (addRT rt) $ cgConst c)
cgBody rt (LOp op args) = do
  z <- mapM (cgBody GetExpBT) args
  pure $ (concat $ map fst z, addRT rt $ cgOp op (map snd z))
cgBody rt LNothing = pure ([], addRT rt JsNull)
cgBody rt (LError x) = pure ([JsError $ JsStr $ T.pack $ x], addRT rt JsNull)
cgBody rt x@(LForeign dres (FStr code) args) = do
  z <- mapM (cgBody GetExpBT) (map snd args)
  let jsArgs = map cgForeignArg (zip (map fst args) (map snd z))
  pure $
    ( concat $ map fst z
    , addRT rt $ cgForeignRes dres $ JsForeign (T.pack code) jsArgs)
cgBody _ x = error $ "Instruction " ++ show x ++ " not compilable yet"

formCon :: Name -> [JsAST] -> State CGBodyState JsAST
formCon n args = do
  case specialCased n of
    Just (ctor, test, match) -> pure $ ctor args
    Nothing -> do
      (conId, arity) <- getConsId n
      if (arity > 0)
        then pure $
             JsObj $
             (T.pack "type", JsInt conId) :
             zip (map (\i -> T.pack $ "$" ++ show i) [1 ..]) args
        else pure $ JsInt conId

formConTest :: Name -> JsAST -> State CGBodyState JsAST
formConTest n x = do
  case specialCased n of
    Just (ctor, test, match) -> pure $ test x
    Nothing -> do
      (conId, arity) <- getConsId n
      if (arity > 0)
        then pure $
             JsBinOp "&&" x $
             JsBinOp "===" (JsProp x (T.pack "type")) (JsInt conId)
        else pure $ JsBinOp "===" x (JsInt conId)

formApp :: LDefs -> Name -> [JsAST] -> JsAST
formApp defs fn argsJS = do
  let alen = length argsJS
  let fname = jsName fn
  case (lookupCtxtExact fn defs) of
    Just (LFun _ _ ps _)
      | (length ps) == 0 && alen == 0 -> JsVar fname
      | (length ps) == 0 && alen > 0 ->
        JsCurryApp (JsVar fname) (drop (length ps) argsJS)
      | (length ps) == alen -> JsApp fname argsJS
      | (length ps) < alen ->
        JsCurryApp
          (JsApp fname (take (length ps) argsJS))
          (drop (length ps) argsJS)
      | (length ps) > alen -> do
        let existings = map (T.pack . ("$h" ++) . show) $ take alen [1 ..]
        let missings =
              map (T.pack . ("$m" ++) . show) $ take ((length ps) - alen) [1 ..]
        JsAppE
          (JsLambda existings $
           JsReturn $
           JsCurryFunExp missings $
           JsApp fname (map JsVar existings ++ map JsVar missings))
          argsJS
    _ -> JsCurryApp (JsVar fname) argsJS

replaceMatchVars :: Name
                 -> JsAST
                 -> Map Text Int
                 -> State CGBodyState (JsAST -> JsAST)
replaceMatchVars n v d = do
  st <- get
  pure $ replaceMatchVars' (defs st) n v d
  where
    replaceMatchVars' :: LDefs
                      -> Name
                      -> JsAST
                      -> Map Text Int
                      -> (JsAST -> JsAST)
    replaceMatchVars' dfs n v d z = transform f z
      where
        formProj :: JsAST -> Int -> JsAST
        formProj v i =
          case specialCased n of
            Just (ctor, test, proj) -> proj v i
            Nothing -> JsProp v (T.pack $ "$" ++ show i)
        f :: JsAST -> JsAST
        f (JsVar x) =
          case Map.lookup x d of
            Nothing -> (JsVar x)
            Just i -> formProj v i
        f x = x

altsRT :: Text -> BodyResTarget -> BodyResTarget
altsRT rn ReturnBT = ReturnBT
altsRT rn (DecVarBT n) = SetVarBT n
altsRT rn (SetVarBT n) = SetVarBT n
altsRT rn GetExpBT = SetVarBT rn

smartif :: JsAST -> JsAST -> Maybe JsAST -> JsAST
smartif cond conseq (Just alt) = JsIf cond conseq (Just alt)
smartif cond conseq Nothing = conseq

cgIfTree :: BodyResTarget
         -> Text
         -> JsAST
         -> [LAlt]
         -> State CGBodyState (Maybe JsAST)
cgIfTree rt resName scrvar ((LConstCase t exp):r) = do
  (d, v) <- cgBody (altsRT resName rt) exp
  alternatives <- cgIfTree rt resName scrvar r
  pure $
    Just $
    smartif (JsBinOp "===" scrvar (cgConst t)) (JsSeq (seqJs d) v) alternatives
cgIfTree rt resName scrvar ((LDefaultCase exp):r) = do
  (d, v) <- cgBody (altsRT resName rt) exp
  pure $ Just $ JsSeq (seqJs d) v
cgIfTree rt resName scrvar ((LConCase _ n args exp):r) = do
  (d, v) <- cgBody (altsRT resName rt) exp
  alternatives <- cgIfTree rt resName scrvar r
  test <- formConTest n scrvar
  replace <-
    replaceMatchVars n scrvar (Map.fromList $ zip (map jsName args) [1 ..])
  let branchBody = JsSeq (seqJs $ map replace d) (replace v)
  pure $ Just $ smartif test branchBody alternatives
cgIfTree _ _ _ [] = pure Nothing

cgForeignArg :: (FDesc, JsAST) -> JsAST
cgForeignArg (FApp (UN "JS_IntT") _, v) = v
cgForeignArg (FCon (UN "JS_Str"), v) = v
cgForeignArg (FCon (UN "JS_Ptr"), v) = v
cgForeignArg (FCon (UN "JS_Unit"), v) = v
cgForeignArg (FApp (UN "JS_FnT") [_, FApp (UN "JS_Fn") [_, _, a, FApp (UN "JS_FnBase") [_, b]]], f) =
  f
cgForeignArg (FApp (UN "JS_FnT") [_, FApp (UN "JS_Fn") [_, _, a, FApp (UN "JS_FnIO") [_, _, b]]], f) =
  JsLambda ["x"] $
  JsReturn $
  cgForeignRes b $
  JsCurryApp (JsCurryApp f [cgForeignArg (a, JsVar "x")]) [JsNull]
cgForeignArg (desc, _) =
  error $ "Foreign arg type " ++ show desc ++ " not supported yet."

cgForeignRes :: FDesc -> JsAST -> JsAST
cgForeignRes (FApp (UN "JS_IntT") _) x = x
cgForeignRes (FCon (UN "JS_Unit")) x = x
cgForeignRes (FCon (UN "JS_Str")) x = x
cgForeignRes (FCon (UN "JS_Ptr")) x = x
cgForeignRes (FCon (UN "JS_Float")) x = x
cgForeignRes desc val =
  error $ "Foreign return type " ++ show desc ++ " not supported yet."

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
cgConst x
  | isTypeConst x = JsInt 0
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
cgOp LStrEq [l, r] = JsB2I $ JsBinOp "==" l r
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
cgOp (LSDiv _) [x, y] = JsBinOp "/" x y
cgOp LWriteStr [_, str] = JsApp "console.log" [str]
cgOp LStrConcat [l, r] = JsBinOp "+" l r
cgOp LStrCons [l, r] = JsForeign "String.fromCharCode(%0) + %1" [l, r]
cgOp (LSRem (ATInt _)) [l, r] = JsBinOp "%" l r
cgOp LCrash [l] = JsErrorExp l
cgOp op exps = error ("Operator " ++ show (op, exps) ++ " not implemented")
