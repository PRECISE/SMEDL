{-# LANGUAGE RecordWildCards #-}

{-# OPTIONS_GHC -fno-warn-orphans #-}

module Arbitrary where

import           Control.Monad.Trans.Class
import           Control.Monad.Trans.Reader
import           Data.Map (Map)
import qualified Data.Map as M
import           Debug.Trace
import           Smedl
import           Test.QuickCheck

overReader :: (Gen a -> Gen b) -> SGen a -> SGen b
overReader f g = (ReaderT . (. runReaderT g)) f

-- Arbitrary instances for fabricating SMEDL objects and values

data Env = Env
    { envVars   :: Map String Type      -- name -> type
    , envEvents :: [EventDef]
    }

genEnv :: Gen Env
genEnv = Env <$> (M.fromList <$> listOf ((,) <$> genIdent <*> arbitrary))
             <*> ((:) <$> arbitrary <*> arbitrary)

type SGen a = ReaderT Env Gen a

runSGen :: SGen a -> Gen a
runSGen act = genEnv >>= runReaderT act

alphabetic :: Gen Char
alphabetic = frequency
    [ (8167,  pure 'a')
    , (1492,  pure 'b')
    , (2782,  pure 'c')
    , (4253,  pure 'd')
    , (12702, pure 'e')
    , (2228,  pure 'f')
    , (2015,  pure 'g')
    , (6094,  pure 'h')
    , (6966,  pure 'i')
    , (0153,  pure 'j')
    , (0772,  pure 'k')
    , (4025,  pure 'l')
    , (2406,  pure 'm')
    , (6749,  pure 'n')
    , (7507,  pure 'o')
    , (1929,  pure 'p')
    , (0095,  pure 'q')
    , (5987,  pure 'r')
    , (6327,  pure 's')
    , (9056,  pure 't')
    , (2758,  pure 'u')
    , (0978,  pure 'v')
    , (2361,  pure 'w')
    , (0150,  pure 'x')
    , (1974,  pure 'y')
    , (0074,  pure 'z') ]

genIdent :: Gen String
genIdent = vectorOf 8 alphabetic

genAtom :: Gen Atom
genAtom = frequency
    [ (1, AInt   <$> choose (1, 100))
    , (1, AFloat <$> choose (1.0, 100.0))
    , (1, AIdent <$> genIdent)
    , (1, ABool  <$> arbitrary)
    , (1, pure ANull) ]

instance Arbitrary Atom where
    arbitrary = trace "Arbitrary Atom" genAtom

genExpr :: Int -> Gen Expr
genExpr 0 = EAtom <$> arbitrary
genExpr depth = frequency
    [ (1, EOr   <$> genExpr d <*> genExpr d)
    , (1, EAnd  <$> genExpr d <*> genExpr d)
    , (1, EEq   <$> genExpr d <*> genExpr d)
    , (1, ENeq  <$> genExpr d <*> genExpr d)
    , (1, ELt   <$> genExpr d <*> genExpr d)
    , (1, ELe   <$> genExpr d <*> genExpr d)
    , (1, EGt   <$> genExpr d <*> genExpr d)
    , (1, EGe   <$> genExpr d <*> genExpr d)
    , (1, EAdd  <$> genExpr d <*> genExpr d)
    , (1, ESub  <$> genExpr d <*> genExpr d)
    , (1, EMul  <$> genExpr d <*> genExpr d)
    , (1, EDiv  <$> genExpr d <*> genExpr d)
    , (1, EMod  <$> genExpr d <*> genExpr d)
    , (1, EPos  <$> genExpr d)
    , (1, ENeg  <$> genExpr d)
    , (1, ECmp  <$> genExpr d)
    , (1, ENot  <$> genExpr d)
    , (1, EAtom <$> arbitrary)
    -- , (1, EIdx  <$> genExpr d <*> choose (1, 10))
    -- , (1, EApp  <$> genExpr d <*> genExpr d)
    -- , (1, EDot  <$> genExpr d <*> genExpr d)
    ]
  where
    d = depth - 1

instance Arbitrary Expr where
    -- arbitrary = trace "Arbitrary Expr" $ genExpr 3
    arbitrary = trace "Arbitrary Expr" $ EAtom <$> arbitrary

instance Arbitrary EventKind where
    arbitrary = trace "Arbitrary EventKind" $  frequency
        [ (1, pure Imported)
        , (1, pure Exported)
        , (1, pure Internal) ]

instance Arbitrary EventDef where
    arbitrary = trace "Arbitrary EventDef" $
        EventDef <$> arbitrary
                 <*> arbitrary
                 <*> genIdent
                 <*> arbitrary
                 <*> arbitrary

instance Arbitrary StateUpdate where
    arbitrary = trace "Arbitrary StateUpdate" $  frequency
        [ (1, SUIncrement <$> genIdent)
        , (1, SUDecrement <$> genIdent)
        , (1, SUAssign    <$> genIdent <*> arbitrary) ]

genAction :: SGen Action
genAction = lift $ frequency
        [ (1, AStateUpdate   <$> arbitrary)
        , (1, ARaiseStmt     <$> genIdent <*> arbitrary)
        -- , (1, AInstantiation <$> genIdent <*> arbitrary)
        -- , (1, ACallStmt      <$> genIdent <*> arbitrary)
        ]

instance Arbitrary Action where
    arbitrary = trace "Arbitrary Action" $  runSGen genAction

genEventInstance :: SGen EventInstance
genEventInstance = do
    Env {..} <- ask
    lift $ EventInstance <$> fmap eventId (elements envEvents)
                         <*> listOf genIdent
                         <*> arbitrary

instance Arbitrary EventInstance where
    arbitrary = trace "Arbitrary EventInstance" $  runSGen genEventInstance

genStep :: SGen Step
genStep = Step <$> genEventInstance <*> overReader listOf genAction

instance Arbitrary Step where
    arbitrary = trace "Arbitrary Step" $  runSGen genStep

genTrace :: [String] -> SGen Trace
genTrace sts = do
    steps <- (:) <$> genStep <*> overReader listOf genStep
    lift $ do
        n <- choose (0, 1) :: Gen Int
        if n == 0
            then Trace <$> elements sts
                       <*> pure steps
                       <*> elements sts
                       <*> pure []
                       <*> pure Nothing
            else Trace <$> elements sts
                       <*> pure steps
                       <*> elements sts
                       <*> arbitrary
                       <*> (Just <$> elements sts)

instance Arbitrary Trace where
    arbitrary = trace "Arbitrary Trace" $  runSGen $ do
        sts <- lift $ (:) <$> genIdent <*> listOf genIdent
        genTrace sts

genScenario :: SGen Scenario
genScenario = do
    sts <- lift $ (:) <$> genIdent <*> listOf genIdent
    Scenario <$> lift arbitrary
             <*> lift genIdent
             <*> ((:) <$> genTrace sts <*> overReader listOf (genTrace sts))

instance Arbitrary Scenario where
    arbitrary = trace "Arbitrary Scenario" $  runSGen genScenario

instance Arbitrary Type where
    arbitrary = trace "Arbitrary Type" $  frequency
        [ (1, pure TInt)
        , (1, pure TFloat)
        , (1, pure TBool)
        , (1, pure TPointer)
        , (1, TUser <$> arbitrary) ]

instance Arbitrary Object where
    arbitrary = trace "Arbitrary Object" $  do
        is <- (M.fromList <$> listOf ((,) <$> genIdent <*> arbitrary))
        env <- genEnv
        Object <$> listOf genIdent
               <*> genIdent
               <*> pure is
               <*> pure (envVars env)
               <*> pure (envEvents env)
               <*> ((:) <$> runReaderT genScenario env
                        <*> listOf (runReaderT genScenario env))

instance Arbitrary Monitor where
    arbitrary = trace "Arbitrary Monitor" $
        Monitor <$> (M.fromList <$> listOf ((,) <$> genIdent <*> arbitrary))
                <*> (M.fromList <$> listOf ((,) <$> genIdent <*> arbitrary))
                <*> (M.fromList <$> listOf ((,) <$> genIdent <*> genIdent))

instance Arbitrary Event where
    arbitrary = trace "Arbitrary Event" $  Event <$> genIdent
                <*> arbitrary
