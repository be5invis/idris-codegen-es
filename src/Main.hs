module Main where

import Idris.AbsSyntax
import Idris.Core.TT
import Idris.ElabDecls
import Idris.Main

import IRTS.CodegenJs
import IRTS.Compiler

import System.Environment
import System.Exit

import Control.Monad

import Paths_idris_codegen_js

data Opts = Opts
  { inputs :: [FilePath]
  , output :: FilePath
  }

showUsage = do
  putStrLn
    "A code generator which is intended to be called by the compiler, not by a user."
  putStrLn "Usage: idris-codegen-js <ibc-files> [-o <output-file>]"
  exitWith ExitSuccess

getOpts :: IO Opts
getOpts = do
  xs <- getArgs
  return $ process (Opts [] "a.out") xs
  where
    process opts ("-o":o:xs) = process (opts {output = o}) xs
    process opts (x:xs) = process (opts {inputs = x : inputs opts}) xs
    process opts [] = opts

js_main :: Opts -> Idris ()
js_main opts = do
  elabPrims
  loadInputs (inputs opts) Nothing
  mainProg <- elabMain
  ir <- compile (Via IBCFormat "js") (output opts) (Just mainProg)
  runIO $ codegenJs ir

main :: IO ()
main = do
  opts <- getOpts
  if (null (inputs opts))
    then showUsage
    else runMain (js_main opts)
