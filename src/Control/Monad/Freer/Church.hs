{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}

module Control.Monad.Freer.Church (
    Free(..)
  ) where

import qualified Control.Monad.Free as M
import           Control.Monad

-- | Church-encoded Freer monad
newtype Free f a = Free
    { runFree :: forall r. (a -> r) -> (forall s. f s -> (s -> r) -> r) -> r
    }

instance Functor (Free f) where
    fmap f x = Free $ \p b -> runFree x (p . f) b

instance Applicative (Free f) where
    pure  = return
    (<*>) = ap

instance Monad (Free f) where
    return x = Free $ \p _ -> p x
    x >>= f  = Free $ \p b -> runFree x (\y -> runFree (f y) p b) b

instance M.MonadFree f (Free f) where
    wrap x = Free $ \p b -> b x $ \y -> runFree y p b
