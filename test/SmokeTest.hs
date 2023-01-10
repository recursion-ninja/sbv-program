import Control.Monad
import Data.List
import Data.SBV
import Data.SBV.Program
import Data.SBV.Program.Examples
import Data.SBV.Program.SimpleLibrary as Lib

main :: IO ()
main = do
  putStrLn "===== exAllProcedure ======"
  r <- exAllProcedure [Lib.and, dec] paperRunningExampleSpec
  case r of
       Right r -> do
         putStrLn $ writePseudocode r
         assert $ solutionCorrect (toIOsList $ sortInstructions r)
       Left e -> error $ show e

  putStrLn "===== standardExAllProcedure ======"
  r <- standardExAllProcedure [Lib.and, dec] paperRunningExampleSpec
  case r of
       Right r -> do
         putStrLn $ writePseudocode r
         assert $ solutionCorrect (toIOsList $ sortInstructions r)
       Left e -> error $ show e

  putStrLn "===== refinedExAllProcedure ======"
  r <- refinedExAllProcedure [Lib.and, dec] paperRunningExampleSpec
  case r of
       Right r -> do
         putStrLn $ writePseudocode r
         assert $ solutionCorrect (toIOsList $ sortInstructions r)
       _ -> error "refinedExAllProcedure"

solutionCorrect s = [0,2] `isPrefixOf` s && ([1,0,2] `isSuffixOf` s || [0,1,2] `isSuffixOf` s)

assert cond = unless cond (error "assertion failed")
