
{-# LANGUAGE DeriveDataTypeable, StandaloneDeriving, OverloadedStrings, DeriveGeneric, DeriveAnyClass, FlexibleInstances #-}

module IRTS.LangTransforms( used_decls
                          ) where


import Control.DeepSeq
import Data.Text (Text)
import qualified Data.Text as T
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Idris.Core.TT
import IRTS.Lang
import Idris.Core.CaseTree
import Data.List
import Data.Maybe
import Control.Monad.Trans.State

import GHC.Generics (Generic)
import Data.Data
import Data.Generics.Uniplate.Data

deriving instance Typeable (LAlt' LExp)
deriving instance Data (LAlt' LExp)
deriving instance Typeable FDesc
deriving instance Data FDesc
deriving instance Typeable LVar
deriving instance Data LVar
deriving instance Typeable PrimFn
deriving instance Data PrimFn
deriving instance Typeable CaseType
deriving instance Data CaseType
deriving instance Typeable LExp
deriving instance Data LExp
deriving instance Typeable LDecl
deriving instance Data LDecl
deriving instance Typeable LOpt
deriving instance Data LOpt

deriving instance NFData FC
deriving instance NFData FC'
deriving instance NFData SpecialName
deriving instance NFData Name
deriving instance Generic LDecl
deriving instance NFData LDecl
deriving instance Generic LOpt
deriving instance NFData LOpt
deriving instance Generic LExp
deriving instance NFData LExp
deriving instance NFData FDesc
deriving instance Generic FDesc
deriving instance NFData ArithTy
deriving instance NFData PrimFn
deriving instance Generic LVar
deriving instance NFData LVar
deriving instance NFData IntTy
deriving instance NFData NativeTy
deriving instance NFData Const
deriving instance NFData CaseType
deriving instance NFData (LAlt' LExp)
deriving instance Generic (LAlt' e)

--data Fun = Fun Name [Name] LExp deriving (Data, Typeable)
--data Con = Con Name Int Int deriving (Data, Typeable)

restrictKeys :: Ord k => Map k a -> Set k -> Map k a
restrictKeys m s = Map.filterWithKey (\k _ -> k `Set.member` s) m

mapMapListKeys :: Ord k => (a->a) -> [k] -> Map k a -> Map k a
mapMapListKeys _ [] x = x
mapMapListKeys f (t:r) x = mapMapListKeys f r $ Map.adjust f t x

{-
getFunctionCallsInExp :: LExp -> [Name]
getFunctionCallsInExp e = [ n | LApp _ n _ <- universe e] ++ [ n | LLazyApp Name [LExp] <- universe e]
-}

{-
used_functions :: Map Name LDecl -> [Name] -> [Name]
used_functions _ [] = []
used_functions alldefs (next_name:rest) =
  let new_names = case Map.lookup next_name alldefs of
                    Just e -> filter (\x -> Map.member x alldefs) (universeBi e) --filter (\x -> Map.member x alldefs) $  getFunctionCallsInExp e
                    _                 -> []
  in next_name : used_functions (Map.delete next_name alldefs) (rest ++ new_names)
-}

extract_globs :: Map Name LDecl -> LDecl -> [Name]
extract_globs dcls (LConstructor _ _ _) = []
extract_globs dcls (LFun _ _ _ e) =
  let f (LV (Glob x)) = Just x
      f (LLazyApp x _) = Just x
      f _ = Nothing
  in [x | Just x <- map f $ universe e, Map.member x dcls]

used_functions :: Map Name LDecl -> Set Name -> [Name] -> [Name]
used_functions _ _ [] = []
used_functions alldefs done names =
  let decls = catMaybes $ map (\x -> Map.lookup x alldefs) names
      used_names = (nub $ concat $ map (extract_globs alldefs) decls) \\ names
      new_names = filter (\x -> not $ Set.member x done) used_names
  in  used_names ++ used_functions alldefs (Set.union done $ Set.fromList new_names) new_names


used_decls :: Map Name LDecl -> [Name] -> [LDecl]
used_decls dcls start =
  let used = reverse $ start ++ used_functions dcls (Set.fromList start) start
  in catMaybes $ map (\x -> Map.lookup x dcls) used

{-
removeUnused :: [(Name, LDecl)] -> Map Name LDecl -> [Name] -> [(Name, LDecl)]
removeUnused dcls dMap start =
  let used = used_functions dMap start
  in filter (\(k, v) -> k `Set.member` used) dcls
-}
