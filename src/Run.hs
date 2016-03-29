{-# LANGUAGE TupleSections #-}
module Run where

import Control.Arrow ( first, second )
import Control.Applicative ( (<$>) )
import Control.DeepSeq ( NFData(..) )
import Control.Monad ( filterM )
import Control.Monad.Trans ( lift )
import Control.Monad.Trans.Maybe ( MaybeT, runMaybeT )
import Data.IORef ( newIORef )
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
import DSL.Expr ( checkType, Type(..), exprSkeleton, Expr(..), reassocExpr )
import DSL.ProcessParse ( lookupNames, netDefinitionToMarkedNet )
import ParseNFA ( textToNFAWB )
import LOLANets ( unparseLOLANet )
import Nets ( NetWithBoundaries(..), net2LLNet, net2LOLANet, MarkedNet
            , net2LLNetWithReadArcs )
import PEPReadArcs ( unparseLLNetWithReadArcs )
import PEP ( unparseLLNet, llNet2Dot, llNet2PNML )
import NFA ( nfaWB2Dot, nfaWB2NFAOutput, nfaWB2NFAReachabilityOutput, NFAWithBoundaries(..)
           , toNFAWithMarking )
import Util ( promptForParam, timeIO, failError, (.:), pretty )
import ProcessExpr
import Debug.Trace

-- TODO: we should really separate the output type from the computation type
data OutputType = Comp_NFA
                | Comp_NFA_FP   -- The new mode in which Penrose will run
                | Comp_Expr     -- mode just to show a skeleton of the resulting expr 
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
        Comp_Expr   -> (compStr, "Show the net which will be evaluated")
    compStr = "Compositional: traverse wiring decomposition, converting to "
              ++ "output,\nexploiting memoisation and language-equivalence."

data RunResult = NFAResult (String, (Counters, Sizes, Bool))
               | NFAResultWFP (String, String)
               | NWBResult String
               | RawResult String
               | NetExprResult (String, String)
               deriving Show

instance NFData RunResult where
    rnf (NFAResult x) = rnf x
    rnf (NFAResultWFP x) = rnf x
    rnf (NWBResult x) = rnf x
    rnf (RawResult x) = rnf x
    rnf (NetExprResult x) = rnf x

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
                -- TODO change name of output function
                Comp_NFA_FP -> goNFA_FP nfaWB2NFAReachabilityOutput
                Comp_NFADot -> goNFA nfaWB2Dot
                Comp_Expr -> goExpr exprSkeleton

  where
    libDir = takeDirectory file </> "lib"

    -- function that is called next
    -- partially apply 'runWith' 
    -- fmt is what to do with the result 
    -- second arg is a pair of the boundaries
    -- third argument is the input file
    goNFA fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NFAResult (first fmt) (expr2NFA getP)
    -- fmt tells us how to format what the main eval function (expr2NFAWFP) returns
    -- input is the file that we do not right now (we are hardcoding the buffer)
    -- getP is the Int that the user passes
    goNFA_FP fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NFAResultWFP fmt (expr2NFAWFP getP)

    goExpr fmt input getP = runWith (findLibraryNFAs libDir) getNFABounds input $
        doOutput NetExprResult (first fmt) convertExpr

    -- What we return after we get the result
    doOutput toRes format convert =
        timeIO . ((toRes . format) <$>) . convert

    getNetBounds (_, NetWithBoundaries l r _ _ _ _) = (l, r)

    getNFABounds (NFAWithBoundaries _ l r) = (l, r)

    -- called by goNFA
    runWith getLib getBounds input outputter = do
        lib <- getLib
        let lookupImport name = lib >>= M.lookup name
            -- parse the input
            compAndWiring = parseComponentsAndWiring input
            -- sugar parsing among other stuff 
            renamed = compAndWiring >>= lookupNames lookupImport
        case renamed of
            Left err -> failError $ "couldn't parse: " ++ err
            Right (expr, _) -> do
                -- do typechecking
                let exprType = checkType getBounds expr
                case exprType of
                    Left err -> failError $ "Couldn't typecheck: "
                                                ++ show err
                    -- interpret and execute
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

-- function for the extra mode
-- we only need the expression produced by the typechecker 
convertExpr :: (Show t) => Expr t -> IO (Expr t, String)
convertExpr expr = return (second show (reassocExpr expr))




