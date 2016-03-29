module Util where

import Control.DeepSeq ( NFData(rnf) )
import Data.List ( intercalate )
import System.CPUTime ( getCPUTime )
import System.Exit ( exitFailure )
import System.IO ( hPutStrLn, stderr )
import Data.IORef ( IORef, readIORef, writeIORef )
import Safe ( readMay )
import Prelude hiding ( unlines )

timeIO :: (NFData a) => IO a -> IO (a, Double)
timeIO action = do
    start <- getCPUTime
    res <- action
    rnf res `seq` return ()
    end <- getCPUTime
    return (res, fromIntegral (end - start) / (10 ^ (12 :: Integer)))

failError :: String -> IO t
failError err = dieWith ("Error: " ++ err)

dieWith :: String -> IO t
dieWith err = hPutStrLn stderr err >> exitFailure

unlines :: [String] -> String
unlines = intercalate "\n"

infixr 8 .:
(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(f .: g) x y = f $ g x y

class (Show a) => Pretty a where
    pretty :: a -> String
    pretty = show

indentLines :: [String] -> String
indentLines = unlines . map (replicate 4 ' ' ++)

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

data ReachabilityResult = 
    FPVerifiable Int | FPUnverifiable Int | FPUnreachable (Maybe Int)

data ReassocResult = ReassocApplied ReassocType | ReassocFail | ReassocNotAttempted

data ReassocType = LeftAssoc | RightAssoc deriving (Eq)

instance Show ReachabilityResult where
    show (FPVerifiable n)   = "Fixed point reached for n = " ++ show n ++ " and system can be globally verified."
    show (FPUnverifiable n) = "Fixed point reached, but reachability fails for n = " ++ show n
    show (FPUnreachable n)  = case n of
        (Just val) -> "Fixed point could not be reached for n = " ++ show val
        Nothing    -> "Fixed point could not be reached"

instance Show ReassocResult where
    show (ReassocApplied a)  = "Reassociation has been applied. The new tree is " ++ show a
    show ReassocFail         = "Reassociation could not be applied for that type of expression."
    show ReassocNotAttempted = "No attemp made to reassociate expression."

instance Show ReassocType where
    show LeftAssoc  = "Left associative"
    show RightAssoc = "Right associative"

(<||>) :: ReassocResult -> ReassocResult -> ReassocResult
(<||>) (ReassocApplied a) _ = (ReassocApplied a)
(<||>) _ (ReassocApplied a) = (ReassocApplied a)
(<||>) _ _                  = ReassocFail

