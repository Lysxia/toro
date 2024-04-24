{-# LANGUAGE
  ConstraintKinds,
  DataKinds,
  FlexibleContexts,
  FlexibleInstances,
  GADTs,
  GeneralizedNewtypeDeriving,
  MultiParamTypeClasses,
  PolyKinds,
  RankNTypes,
  TypeOperators #-}
module Toro.EffectfulOverBluefin where

import Data.Kind (Type)
import qualified Bluefin.Eff as B
import qualified Bluefin.State as B

type Effect = B.Effects -> Type

data Env (hs :: [Effect]) (ε :: B.Effects) where
  Nil :: Env '[] ε
  (:.) :: h ε -> Env hs ε' -> Env (h ': hs) (ε B.:& ε')

newtype Eff hs a = Eff { unEff :: forall ε. Env hs ε -> B.Eff ε a }

data SomeHandle (h :: Effect) (ε :: B.Effects) where
  SomeHandle :: ε0 B.:> ε => h ε0 -> SomeHandle h ε

class h :> hs where
  lookupEnv :: Env hs ε -> SomeHandle h ε

instance {-# OVERLAPPING #-} h :> (h ': hs) where
  lookupEnv (h :. _) = SomeHandle h

instance h :> hs => h :> (h' ': hs) where
  lookupEnv (_ :. hs) = case lookupEnv hs of
    SomeHandle h -> SomeHandle h

withHandle :: h :> hs => (forall ε ε'. ε' B.:> ε => h ε' -> B.Eff ε a) -> Eff hs a
withHandle f = Eff (\env -> case lookupEnv env of
  SomeHandle h -> f h)

type State = B.State

get :: State s :> hs => Eff hs s
get = withHandle (\state -> B.get state)

put :: State s :> hs => s -> Eff hs ()
put s = withHandle (\state -> B.put state s)

runPureEff :: Eff '[] a -> a
runPureEff m = B.runPureEff (unEff m Nil)

runState :: Eff (State s ': hs) a -> s -> Eff hs (a, s)
runState m s = Eff (\env -> B.runState s (\state -> unEff m (state :. env)))
