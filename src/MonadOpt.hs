module MonadOpt where

import Control.Monad.State
import Lang
import Control.Monad

data StateOpt = StateOpt {
  opt :: Int,
  nenv :: [Name]
}

newtype Changes a = Changes { runChanges :: StateOpt -> (a, StateOpt) }

class Monad m => MonadOptimization m where
    -- Agrega el cambio al total de optimizaciones
    add :: Int -> m ()
    -- Devuelve el total de optimizaciones
    total :: m Int
    update :: Name -> m ()
    getNEnv :: m [Name]

instance Monad Changes where
    return x = Changes (\i -> (x, i))
    m >>= f = Changes (\i -> let (x, i') = runChanges m i in runChanges (f x) i')

instance Functor Changes where
    fmap = liftM

instance Applicative Changes where
    pure  = return
    (<*>) = ap

instance MonadOptimization Changes where
    add x = Changes (\i -> ((), i {opt = x + opt i}))
    total = Changes (\i -> (opt i, i))
    update n = Changes (\i -> ((), i {nenv = n : nenv i}))
    getNEnv = Changes (\i -> ((nenv i), i))
