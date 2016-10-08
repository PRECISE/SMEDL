{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Arbitrary
import Control.Exception
import Control.Logging
import Data.Char
import Data.String.Here
import Debug.Trace
import Prelude hiding (log)
import Smedl
import System.Environment
import Test.Hspec
-- import Test.Hspec.Expectations.Lifted
import Test.QuickCheck
import Text.Parsec

main :: IO ()
main = do
    args <- getArgs
    case args of
        file:_ -> parseFile file
        _ -> tests

tests :: IO ()
tests = hspec $ do
    describe "basic parsing" $ do
        it "succeeds at parsing a basic SMEDL object" $ do
            let doc = [here|
object Basic
identity
  pointer data;
  int num;
state
  int x, y, total;
events
  imported upX(), upY();
  internal upTotal(int);
scenarios
  main:
    X -> upX() {raise upTotal(1)} -> Y
    Y -> upY() {raise upTotal(2)} -> X
  total:
    Run -> upTotal(x) when this.total < 10 { total++ } -> Run
      else -> Stop
|]
            parse parseObject "here doc" doc
                `shouldSatisfy` \(Left _) -> True
{-
        it "succeeds at parsing a specific object" $ do
            let doc = [here|
object aascllwl
state
  bool nlenshiy;
events
  imported error swehegge() = 22.232302490215563;
scenarios
  bhnaetca:
    fpintanv -> swehegge(hhobnhnt) when true -> fpintanv
             else -> erloecst
  iehnfptc:
    arhaessv -> swehegge when null { ejdakttm-- } -> arhaessv
    arhaessv -> swehegge(aaahfdui) when null { raise ellaedkn(95) }
             -> swehegge when esteitca -> arhaessv
|]
            parse parseObject "here doc" doc
                `shouldSatisfy` \(Right _) -> True
        it "parses generated objects" $ property $ \(x :: Object) ->
            traceShow x $
            traceShow (parse parseObject "generated" (show x)) $
            Right x == parse parseObject "generated" (show x)
-}

parseFile :: String -> IO ()
parseFile path = do
    contents <- readFile path
    parseTest parseObject contents
