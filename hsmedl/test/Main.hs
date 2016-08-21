{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes #-}

module Main where

import Control.Exception
import Control.Logging
import Smedl
import Data.Char
import Data.String.Here
import Prelude hiding (log)
import Test.Hspec

tryAny :: IO a -> IO (Either SomeException a)
tryAny = try

main :: IO ()
main = withStdoutLogging $ hspec $ do
    describe "issues" $ do
        it "#25" $ do
            True == True
