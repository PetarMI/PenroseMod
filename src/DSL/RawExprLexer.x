{
{-# OPTIONS_GHC -w #-}
module DSL.RawExprLexer
    ( lexer
    , LexerTok(..)
    ) where

import Data.Text.Lazy ( fromStrict )
import Data.Text.Lazy.Encoding ( encodeUtf8 )
import Data.ByteString.Lazy ( ByteString )
import Data.ByteString.Lazy.Char8 ( unpack )
}

%wrapper "basic-bytestring"

$digit = 0-9
$nonzerodigit = 1-9
$res = [λ\.\\\(\)=\*]

tokens :-
    $white+               ;
    \-\-.*                ;
    ⊗ | \*                { const TokTens }
    \;                    { const TokSeq }
    :                     { const TokColon }
    \->                   { const TokArr }
    Int                   { const TokIntType }
    Net                   { const TokNet }
    bind                  { const TokBind }
    read                  { const TokRead }
    =                     { const TokEq }
    in                    { const TokIn  }
    λ | \\                { const TokLambda }
    \.                    { const TokDotSep }
    n_sequence            { const TokSequence }
    \*\*                  { const TokKStar }
    0                     { const (TokNum 0) }
    $nonzerodigit $digit* { TokNum . read . unpack }
    intcase               { const TokIntCase }
    starcase              { const TokStarCase }
    \+                    { const TokPlus }
    \-                    { const TokMinus }
    \(                    { const TokLPar }
    \)                    { const TokRPar }
    . # $res # $white+    { \bs -> TokName (unpack bs) }

{
data LexerTok = TokTens
              | TokSeq
              | TokBind
              | TokColon
              | TokArr
              | TokNet
              | TokIntType
              | TokEq
              | TokIn
              | TokRead
              | TokLambda
              | TokDotSep
              | TokSequence
              | TokKStar
              | TokLPar
              | TokRPar
              | TokNum Int
              | TokIntCase
              | TokStarCase
              | TokPlus
              | TokMinus
              | TokName String
              deriving (Show)

lexer = alexScanTokens . encodeUtf8 . fromStrict
}
