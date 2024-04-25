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
import qualified Bluefin.Internal as B (Eff(UnsafeMkEff,unsafeUnEff), unsafeRemoveEff)
import qualified Bluefin.Eff as B
import qualified Bluefin.State as B
import qualified Toro.BluefinExtras as B
import Toro.BluefinExtras (HEffect)
import Unsafe.Coerce (unsafeCoerce)

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

type HandleOf = B.HandleOf

interpret ::
  (forall x. f x -> Eff es x) ->
  Eff (HandleOf f ': es) a ->
  Eff es a
interpret g (Eff m) = Eff (\env ->
  B.interpret (\f -> unEff (g f) env) (\h -> m (h :. env)))

type HHandler f es = forall es0.
  (forall y. Eff es0 y -> Eff es y) ->
  forall x. f (Eff es0) x -> Eff es x

data HHandleOf (f :: HEffect) (ε :: B.Effects) where
  UnsafeHHandleOf :: (forall es0 x. f (Eff es0) x -> Eff es0 x) -> HHandleOf f ε

unsafeRescopeEnv :: Env hs ε -> Env hs ε'
unsafeRescopeEnv = unsafeCoerce

hinterpret ::
  HHandler f es ->
  Eff (HHandleOf f ': es) a ->
  Eff es a
hinterpret g (Eff m) = Eff (\env ->
  B.unsafeRemoveEff (m (
       UnsafeHHandleOf (\f -> Eff (\env0 -> unEff (g (unliftEff env0) f) (unsafeRescopeEnv env)))
    :. env)))
  where
    unliftEff env (Eff n) = Eff (\_ -> B.UnsafeMkEff (B.unsafeUnEff (n env)))

type HHandler' f es = forall es0.
  (forall y. Eff es y -> Eff es0 y) ->
  forall x. f (Eff es0) x -> Eff es0 x

data HHandleOf' (f :: HEffect) (ε :: B.Effects) where
  UnsafeHHandleOf' :: (forall es0 x. f (Eff es0) x -> Eff es0 x) -> HHandleOf' f ε

hinterpret' ::
  HHandler' f es ->
  Eff (HHandleOf' f ': es) a ->
  Eff es a
hinterpret' g (Eff m) = Eff (\env ->
  B.unsafeRemoveEff (m (
       UnsafeHHandleOf' (g (liftEff env))
    :. env)))
  where
    liftEff env (Eff n) = Eff (\_ -> B.UnsafeMkEff (B.unsafeUnEff (n env)))
