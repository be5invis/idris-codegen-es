{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, OverloadedStrings, DeriveGeneric, DeriveAnyClass #-}

module IRTS.DJsTransforms( inline
                         , removeUnused
                         , isTailRecursive
                         , inlineCons
                         , Con(..)
                         , Fun(..)
                         ) where

import Debug.Trace

import Control.DeepSeq
import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import IRTS.Defunctionalise
import Idris.Core.TT
import Idris.Core.CaseTree
import Data.List
import Control.Monad.Trans.State

import GHC.Generics (Generic)
import Data.Data
import Data.Generics.Uniplate.Data

deriving instance Typeable DAlt
deriving instance Data DAlt
deriving instance Typeable FDesc
deriving instance Data FDesc
deriving instance Typeable LVar
deriving instance Data LVar
deriving instance Typeable PrimFn
deriving instance Data PrimFn
deriving instance Typeable CaseType
deriving instance Data CaseType
deriving instance Typeable DExp
deriving instance Data DExp
deriving instance Typeable DDecl
deriving instance Data DDecl

deriving instance NFData FC
deriving instance NFData FC'
deriving instance NFData SpecialName
deriving instance NFData Name
deriving instance Generic Fun
deriving instance NFData Fun
deriving instance Generic DExp
deriving instance NFData DExp
deriving instance NFData FDesc
deriving instance Generic FDesc
deriving instance NFData ArithTy
deriving instance NFData PrimFn
deriving instance Generic LVar
deriving instance NFData LVar
deriving instance NFData IntTy
deriving instance NFData NativeTy
deriving instance NFData Const
deriving instance Generic DAlt
deriving instance NFData DAlt
deriving instance NFData CaseType

data Fun = Fun Name [Name] DExp deriving (Data, Typeable)
data Con = Con Name Int Int deriving (Data, Typeable)

data InlinerState = InlinerState { lastInt :: Int
                                 --, callGraph :: Map Name [Name]
                                 --, funDecls :: Map Name Fun
                                 } deriving (Generic, NFData)

restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m

mapMapListKeys :: Ord k => (a->a) -> [k] -> Map k a -> Map k a
mapMapListKeys _ [] x = x
mapMapListKeys f (t:r) x = mapMapListKeys f r $ Map.adjust f t x

used_functions :: Map Name Fun -> [Name] -> Set Name
used_functions _ [] = Set.empty
used_functions alldefs (next_name:rest) =
  let new_names = case Map.lookup next_name alldefs of
                    Just (Fun _ _ e) -> filter (\x -> Map.member x alldefs) $ getFunctionCallsInExp e
                    _                 -> []
  in Set.insert next_name $ used_functions (Map.delete next_name alldefs) (rest ++ new_names)

removeUnused ::  Map Name Fun -> [Name] -> Map Name Fun
removeUnused funMap start =
  let used = used_functions funMap start
  in Map.filterWithKey (\k v -> k `Set.member` used) funMap

inlineCons :: Map Name Fun -> Map Name Con -> Map Name Fun
inlineCons x y =
  Map.map (transformBi f) x
  where
    f x@(DApp b n args) =
      case Map.lookup n y of
        Just (Con n' conId j) -> DC Nothing conId n args
        _ -> x
    f x = x

inline :: Map Name Fun -> Map Name Fun
inline x = evalState (inline' x) (InlinerState {lastInt = 0})

inline' :: Map Name Fun -> State InlinerState (Map Name Fun)
inline' decls =
  do
    let calls = getFunctionCallGraph decls
    let funsToInline = Map.keysSet $ Map.filterWithKey (\k v -> length v == 1 && not (k `elem` v)) calls
    funsToInlineDefs <- mapM (\(Fun x y z) -> Fun x y <$> renameForInline z) $
                            restrictKeys decls funsToInline
    inlineFunctions funsToInlineDefs decls
    --res <- inlineAll debug (InlinerState 0 calls decls)
    --pure $ funDecls res
{-
inlineAll ::  Map Name Fun -> Map Name Fun -> State InlinerState (Map Name Fun)
inlineAll  =
  do
    case Map.keys $ Map.filterWithKey (\k v -> length v == 1 && not (k `elem` v)) (callGraph st) of
      t:_ ->
        do
          let ((), st') = runState (inlineFunction t) st
          st' `deepseq` if debug then putStrLn $ "Finished inlining " ++ show t else pure ()
          inlineAll debug st'
      [] ->
        pure st
-}

inlineFunctions :: Map Name Fun -> Map Name Fun -> State InlinerState (Map Name Fun)
inlineFunctions toInline decls =
  sequence $ Map.map (\(Fun x y z) -> Fun x y <$> (transformM (f toInline) z) ) decls
  where
    f :: Map Name Fun -> DExp -> State InlinerState DExp
    f d x@(DApp b n argVals) =
      case Map.lookup n d of
        Just (Fun _ argNames def) ->
          do
            newNames <- getNewNames $ length argNames
            pure $ foldl'
                    (\e (n, ae) -> DLet n ae e)
                    (switchNames (Map.fromList $ zip argNames newNames) def)
                    (reverse $ zip newNames argVals)
        _ ->
          pure x
    f d x = pure x


getNewNames :: Int -> State InlinerState [Name]
getNewNames n =
  do
    st <- get
    let lasti = lastInt st
    put $ st {lastInt = lasti + n}
    pure $ map (\x -> MN x "idris_js_inliner") [(lasti+1)..(lasti + n)]

{-
updateFnExp :: Name -> [Name] -> DExp -> DExp -> State InlinerState ()
updateFnExp n args def e =
  do
    st <- get
    let cleanCallGraph = mapMapListKeys (filter (/=n)) (getFunctionCallsInExp def) (callGraph st)
    let newCallGraph =  mapMapListKeys (n:) (getFunctionCallsInExp e) cleanCallGraph
    put $ st {callGraph = newCallGraph, funDecls = Map.insert n (Fun n args e) (funDecls st)}


inlineFnOnFn :: Name -> [Name] -> DExp -> Name -> State InlinerState ()
inlineFnOnFn n args def x =
  do
    argNames <- getNewNames $ length args
    st <- get
    case Map.lookup x (funDecls st) of
      Just (Fun _ xargs xdef) ->
        let newXdef = transform (f argNames) xdef
        in updateFnExp x xargs xdef newXdef
      _ ->
        pure ()
  where
    replaceArgs reps x@(DV (Glob n')) =
      case Map.lookup n' reps of
        Nothing -> x
        Just e -> e
    replaceArgs _ x = x

    f argN x@(DApp b' n' args') =
      if n' == n then
        foldl'
          (\e (n, ae) -> DLet n ae e)
          (transform (replaceArgs $ Map.fromList $ zip args (map (DV . Glob) argN)) def)
          (reverse $ zip argN args')
        else x
    f _ x = x
-}

renameForInline :: DExp -> State InlinerState DExp
renameForInline x =
  do
    let lets = [ n | DLet n _ _ <- universe x]
    let patterNames = concat $ [ ns | DConCase _ _ ns _ <- universeBi x]
    let allNames = lets ++ patterNames
    newNames <- getNewNames $ length allNames
    let dic = Map.fromList $ zip allNames newNames
    pure $ switchNames dic x

switchNames :: Map Name Name -> DExp -> DExp
switchNames d z =
  transformBi (f d) z
  where
    f d x =
      case Map.lookup x d of
        Nothing -> x
        Just z -> z

{-
inlineFunction :: Name -> State InlinerState ()
inlineFunction n =
  do
    st <- get
    case (Map.lookup n (callGraph st), Map.lookup n (funDecls st)) of
      (Just x, Just (Fun _ args def)) ->
        do
          def' <- renameForInline def
          mapM_ (\z -> inlineFnOnFn n args def' z) x
      _ ->
        pure ()
-}


isRecursive :: Name -> DExp -> Bool
isRecursive n ex = n `elem` universeBi ex

isTailRecursive :: Name -> DExp -> Bool
isTailRecursive n ex = n `elem` [ n' | DApp True n' _ <- universe ex]

getFunctionCallsInExp :: DExp -> [Name]
getFunctionCallsInExp e = [ n | DApp _ n _ <- universe e]

getFunctionCallGraph :: Map Name Fun -> Map Name [Name]
getFunctionCallGraph decls =
  Map.foldl' (\x v -> procDecl v x) Map.empty decls
  where
    procDecl :: Fun -> Map Name [Name] -> Map Name [Name]
    procDecl (Fun nf _ e) x = foldl' (\calls z -> Map.insertWith (++) z [nf] calls) x (getFunctionCallsInExp e) -- (universeBi e)
