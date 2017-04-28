{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}

module IRTS.CodegenEs.JsName
  ( jsName
  , jsNameGenerated
  ) where

import Data.Char
import Data.List
import qualified Data.Map.Strict as Map
import Data.Text (Text)
import qualified Data.Text as T
import IRTS.CodegenEs.JsAST
import Idris.Core.TT

jsEscape :: String -> String
jsEscape = concatMap jschar
  where
    jschar x
      | isAlpha x || isDigit x = [x]
      | x == '.' = "__"
      | otherwise = "_" ++ show (fromEnum x) ++ "_"

showCGJS :: Name -> String
showCGJS (UN n) = T.unpack n
showCGJS (NS n s) = showSep "." (map T.unpack (reverse s)) ++ "." ++ showCGJS n
showCGJS (MN _ u)
  | u == txt "underscore" = "_"
showCGJS (MN i s) = "{" ++ T.unpack s ++ "_" ++ show i ++ "}"
showCGJS (SN s) = showCGJS' s
  where
    showCGJS' (WhereN i p c) =
      "where{" ++ showCGJS p ++ ";" ++ showCGJS c ++ ";" ++ show i ++ "}"
    showCGJS' (WithN i n) = "_" ++ "with{" ++ showCGJS n ++ ";" ++ show i ++ "}"
    showCGJS' (ImplementationN cl impl) =
      "impl{" ++ showCGJS cl ++ ";" ++ showSep ";" (map T.unpack impl) ++ "}"
    showCGJS' (MethodN m) = "meth{" ++ showCGJS m ++ "}"
    showCGJS' (ParentN p c) = "par{" ++ showCGJS p ++ ";" ++ show c ++ "}"
    showCGJS' (CaseN fc c) = "case{" ++ showCGJS c ++ ";" ++ showFC' fc ++ "}"
    showCGJS' (ElimN sn) = "elim{" ++ showCGJS sn ++ "}"
    showCGJS' (ImplementationCtorN n) = "ictor{" ++ showCGJS n ++ "}"
    showCGJS' (MetaN parent meta) =
      "meta{" ++ showCGJS parent ++ ";" ++ showCGJS meta ++ "}"
    showFC' (FC' NoFC) = ""
    showFC' (FC' (FileFC f)) = "_" ++ cgFN f
    showFC' (FC' (FC f s e))
      | s == e = "_" ++ cgFN f ++ "_" ++ show (fst s) ++ "_" ++ show (snd s)
      | otherwise =
        "_" ++
        cgFN f ++
        "_" ++
        show (fst s) ++
        "_" ++ show (snd s) ++ "_" ++ show (fst e) ++ "_" ++ show (snd e)
    cgFN =
      concatMap
        (\c ->
           if not (isDigit c || isLetter c)
             then "__"
             else [c])
showCGJS (SymRef i) = error "can't do codegen for a symbol reference"

jsName :: Name -> Text
jsName n =
  let name = showCGJS n
  in T.pack $ jsEscape name

jsNameGenerated :: Int -> Text
jsNameGenerated v = T.pack $ "$idris_" ++ show v
