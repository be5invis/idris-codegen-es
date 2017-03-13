{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, OverloadedStrings #-}

module IRTS.DJsTransforms( inline
                         , removeUnused
                         , isTailRecursive
                         , inlineCons
                         , Con(..)
                         , Fun(..)
                         ) where


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


data Fun = Fun Name [Name] DExp deriving (Data, Typeable)
data Con = Con Name Int Int deriving (Data, Typeable)

used_functions_exp :: DExp -> [Name]
used_functions_exp x =
  nub $ universeBi x

used_functions :: Map Name Fun -> [Name] -> Set Name
used_functions _ [] = Set.empty
used_functions alldefs (next_name:rest) =
  let new_names = case Map.lookup next_name alldefs of
                    Just (Fun _ _ e) -> filter (\x -> Map.member x alldefs) $ used_functions_exp e
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
inline decls =
    let callCount = functionCalls decls
        toInline = Map.keys $ Map.filter (==1) callCount
        stInl = foldl' (\x y -> do z<-x; inlineFn y z) (pure decls) toInline
    in evalState stInl 0 --foldl' (\x y -> inlineFn y x) decls toInline

renameLoc :: Int -> LVar -> LVar
renameLoc i (Glob x) = Glob x
renameLoc i (Loc j) = Loc $ i + j

getNewNames :: Int -> State Int [Name]
getNewNames n =
  do
    lasti <- get
    put $ lasti + n
    pure $ map (\x -> MN x "idris_js_inliner") [(lasti+1)..(lasti + n)]

inlineFnExp :: Name -> [Name] -> DExp -> DExp -> State Int DExp
inlineFnExp n args def ex =
  do
    argNames <- getNewNames $ length args
    pure $ transform (f argNames) ex
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
          (zip argN args')
        else x
    f _ x = x

inlineFnDec :: Name -> [Name] -> DExp -> Fun -> State Int Fun
inlineFnDec n args def (Fun b a e) = Fun b a <$> inlineFnExp n args def e

isRecursive :: Name -> DExp -> Bool
isRecursive n ex = n `elem` universeBi ex

isTailRecursive :: Name -> DExp -> Bool
isTailRecursive n ex = n `elem` [ n' | DApp True n' _ <- universe ex]

inlineFn :: Name -> Map Name Fun -> State Int (Map Name Fun)
inlineFn n decls =
  case Map.lookup n decls of
    Just (Fun _ args def) ->
      do
        afterInlne <- sequence $ Map.map (inlineFnDec n args def) decls
        if isRecursive n def then
            pure afterInlne
          else pure $ Map.delete n afterInlne
    _ -> pure decls


functionCalls :: Map Name Fun -> Map Name Int
functionCalls decls =
  Map.foldl' (\x v -> procDecl v x) Map.empty decls
  where
    procDecl :: Fun -> Map Name Int -> Map Name Int
    procDecl (Fun _ _ e) x = foldl' (\counts z -> Map.insertWith (+) z 1 counts) x (universeBi e)
