{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleInstances,
  GADTs,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  PolyKinds,
  RankNTypes,
  TypeOperators #-}
module Toro.BluefinOverEffectful (Eff, runPure, type (:&), type (:>), State, runState, get, put) where

import Data.Type.Equality
import qualified Effectful as E
import qualified Effectful.State.Dynamic as E

newtype Eff ε a = Eff { unEff :: E.Eff ε a }
  deriving (Functor, Applicative, Monad)

runPure :: Eff '[] a -> a
runPure (Eff m) = E.runPureEff m

type (:&) = '(:)

class η E.:> ε => η :> ε where
instance η :> (η ': ε) where
instance {-# INCOHERENT #-} η :> ε => η :> (η2 ': ε) where

newtype State s η = State (η :~: E.State s)

runState :: (forall η. State s η -> Eff (η :& ε) a) -> s -> Eff ε (a, s)
runState f s = Eff (E.runStateLocal s (unEff (f (State Refl))))

get :: η :> ε => State s η -> Eff ε s
get (State Refl) = Eff E.get

put :: η :> ε => State s η -> s -> Eff ε ()
put (State Refl) s = Eff (E.put s)

example :: Eff ε Int
example = do
  (((), ny), nx) <- (`runState` 1) (\x ->
                    (`runState` 10) (\y -> do
                        get x >>= \n -> put x (2 * n)
                        get y >>= \n -> put y (2 * n)))
  pure (nx + ny)
