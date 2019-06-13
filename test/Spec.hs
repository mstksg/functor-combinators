{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

import           Test.Tasty
import           Tests.HBifunctor

-- retractingProp
--     :: forall t f m a. (Interpret t, C t f, Show (f a), Show (t f a), Eq (f a), Monad m)
--     => Gen (f a)
--     -> PropertyT m ()
-- retractingProp gx = do
--     x <- forAll gx
--     tripping x (inject @t) (Just . retract)

-- prop_retract_Free :: Property
-- prop_retract_Free = property $
--     retractingProp @Free listGen

-- tests :: IO Bool
-- tests = checkParallel $$(discover)

-- main :: IO ()
-- main = defaultMain [tests]

-- -- import           Test.Tasty.Hedgehog
-- -- import           Test.Tasty.Ingredients.ConsoleReporter
-- import           Test.Tasty
-- import           Tests.IntMap
-- import           Tests.IntSet
-- import           Tests.Map
-- import           Tests.Sequence
-- import           Tests.Set

-- setOpts :: TestTree -> TestTree
-- setOpts = id
-- -- setOpts = localOption (HedgehogTestLimit    (Just 500))
-- --         . localOption (HedgehogDiscardLimit (Just 500))
-- --         . localOption (HideSuccesses        True      )

main :: IO ()
main = defaultMain $
            testGroup "Tests" [ hbifunctorTests
                              ]

