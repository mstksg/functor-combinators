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
import           Tests.HFunctor

main :: IO ()
main = defaultMain $
            testGroup "Tests" [ hfunctorTests
                              , hbifunctorTests
                              ]

