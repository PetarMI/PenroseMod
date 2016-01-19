{-# LANGUAGE TupleSections #-}
module Run where

import Control.Arrow ( first )
import Control.Applicative ( (<$>) )
import Control.DeepSeq ( NFData(..) )
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe ( MaybeT, runMaybeT )
import Data.IORef ( newIORef, IORef, readIORef, writeIORef )
import Data.Map.Strict ( Map )
import qualified Data.Map as M ( fromList, lookup )
import Data.Maybe ( fromMaybe )
import qualified Data.Text as T
import qualified Data.Text.IO as DTIO
import Safe ( readMay )
import System.Directory ( doesFileExist, doesDirectoryExist
                        , getDirectoryContents )
import System.FilePath ( (</>), takeExtension, dropExtension, takeFileName
                       , takeDirectory )
import System.PosixCompat.Files ( isRegularFile, getFileStatus )

import DSL.ComponentsAndWiringParser ( parseComponentsAndWiring
                                     , parseNetDefinition )
import DSL.Expr ( checkType, Type(..) )
import DSL.ProcessParse ( lookupNames, netDefinitionToMarkedNet )
import ParseNFA ( textToNFAWB )
import LOLANets ( unparseLOLANet )
import Nets ( NetWithBoundaries(..), net2LLNet, net2LOLANet, MarkedNet
            , net2LLNetWithReadArcs )
import PEPReadArcs ( unparseLLNetWithReadArcs )
import PEP ( unparseLLNet, llNet2Dot, llNet2PNML )
import NFA ( nfaWB2Dot, nfaWB2NFAOutput, NFAWithBoundaries(..)
           , toNFAWithMarking )
import Util ( timeIO, failError, (.:), pretty )
import ProcessExpr

-- TODO: we should really separate the output type from the computation type
data OutputType = Comp_NFA
                | Comp_NFA_FP   -- The new mode in which Penrose will run
                | Comp_NFADot
                deriving (Read, Show)

-- some function telling more about the output type selected by the user
outputTypeDoc :: OutputType -> String
outputTypeDoc outType = header ++ "\n" ++ detail ++ ".\n"
  where
    (header, detail) = case outType of
        Comp_NFA -> (compStr, "NFA format, used to import pre-computed NFAs "
                              ++ "for commonly used components")
        Comp_NFA_FP -> (compStr, "NFA format, used to import pre-computed NFAs "
                              ++ "using Fixed-point checking for reachability")
        Comp_NFADot -> (compStr, "DOT format representation of resulting "
                                 ++ "(reduced) NFA")
    compStr = "Compositional: traverse wiring decomposition, converting to "
              ++ "output,\nexploiting memoisation and language-equivalence."

data RunResult = NFAResult (String, (Counters, Sizes, Bool))
               | NFAResultWFP (String, (Counters, Sizes, Bool))
               | NWBResult String
               | RawResult String
               deriving Show

instance NFData RunResult where
    rnf (NFAResult x) = rnf x
    rnf (NFAResultWFP x) = rnf x
    rnf (NWBResult x) = rnf x
    rnf (RawResult x) = rnf x

runner :: OutputType -> FilePath -> Maybe [Int] -> IO (RunResult, Double)
runner outputType file mbParams = do
    exists <- doesFileExist file
    if not exists
        then failError $ "input file: " ++ file ++ " doesn't exist!"
        else do
            input <- DTIO.readFile file
            ref <- newIORef (fromMaybe [] mbParams)
            let getP = promptForParam ref
            -- anonymous function that is passed a function 'f' as a parameter
            -- 'f' comes as the result from the correct case statement
            -- for the base case 'f' is the result from 'goNFA nfaWB2NFAOutput'
            -- the function body becomes -> goNFA nfaWB2NFAOutput input getP
            -- input is the file that is read (nets and wiring)
            -- getP is the number of nets that is taken as user input. Here it is passed as IO Int
            -- now go to line 135
            (\f -> f input getP) $ case outputType of
                -- this is the case that we go to
                -- partially apply goNFA with nfaWB2NFAOutput
                -- nfaWB2NFAOutput is some datatype
                Comp_NFA -> goNFA nfaWB2NFAOutput
                Comp_NFA_FP -> goNFA_FP nfaWB2NFAOutput
                Comp_NFADot -> goNFA nfaWB2Dot
  where
    libDir = takeDirectory file </> "lib"

    -- function that is called next
    -- partially apply 'runWith' 
    -- fmt is what to do with the result 
    -- second arg is a pair of the boundaries
    -- third argument is the input file
    -- How do we get expr2NFA from doOutput
    goNFA fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NFAResult (first fmt) (expr2NFA getP)
    -- goNFA copy that works with fixed points. It doesnt need runWith for now as it doesnt parse anything
    -- fmt tells us how to format what the main eval function (expr2NFAWFP) returns
    -- input is the file that we do not right now (we are hardcoding the buffer)
    -- getP is the Int that the user passes
    -- goNFA_FP fmt input getP = doOutput NFAResult_WFP (first fmt) (expr2NFAWFP getP)
    goNFA_FP fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NFAResultWFP (first fmt) (expr2NFAWFP getP)

    -- What we return after we get the result
    doOutput toRes format convert =
        timeIO . ((toRes . format) <$>) . convert

    getNetBounds (_, NetWithBoundaries l r _ _ _ _) = (l, r)

    getNFABounds (NFAWithBoundaries _ l r) = (l, r)

    -- called by goNFA
    -- not sure what outputter does
    runWith getLib getBounds input outputter = do
        lib <- getLib
        let lookupImport name = lib >>= M.lookup name
            compAndWiring = parseComponentsAndWiring input
            renamed = compAndWiring >>= lookupNames lookupImport
        case renamed of
            Left err -> failError $ "couldn't parse: " ++ err
            Right (expr, _) -> do
                let exprType = checkType getBounds expr
                case exprType of
                    Left err -> failError $ "Couldn't typecheck: "
                                                ++ show err
                    Right (expr', TyArr _ _) -> outputter expr'
                    Right ty -> failError $
                        "Top-level expr must be base type, got: "++ show ty

type LibraryMap p = Map String p

findLibraryNFAs :: FilePath -> IO (Maybe (LibraryMap (NFAWithBoundaries Int)))
findLibraryNFAs libDir = findThings libDir "nfa" (textToNFAWB . T.lines)

findLibraryNWBs :: FilePath -> IO (Maybe (LibraryMap MarkedNet))
findLibraryNWBs libDir = findThings libDir "nwb" $ \input ->
    either error snd $ parseNetDefinition input >>= netDefinitionToMarkedNet

findThings :: FilePath -> String -> (T.Text -> t) -> IO (Maybe (LibraryMap t))
findThings libDir extension parseThing = runMaybeT $ do
    files <- getLibraryContents libDir
    let things = filter ((== ('.' : extension)) . takeExtension) files
        getter n = do
            thing <- lift $ (parseThing <$>) . DTIO.readFile $ n
            return (toFileName n, thing)
    M.fromList <$> mapM getter things

toFileName :: FilePath -> FilePath
toFileName = dropExtension . takeFileName

getLibraryContents :: FilePath -> MaybeT IO [FilePath]
getLibraryContents dir = do
    exists <- lift $ doesDirectoryExist dir
    if not exists
        then fail "missing lib dir"
        else lift $ do
            contents <- map (dir </>) <$> getDirectoryContents dir
            filterM ((isRegularFile <$>) . getFileStatus) contents

promptForParam :: IORef [Int] -> IO Int
promptForParam ref = do
    is <- readIORef ref
    case is of
        [] -> getInt
        (x:xs) -> writeIORef ref xs >> return x
  where
    getInt :: IO Int
    getInt = do
        putStrLn "Enter a number for PARAM"
        line <- getLine
        case readMay line of
            Just x -> return x
            Nothing -> putStrLn "Invalid number, try again!" >> getInt

