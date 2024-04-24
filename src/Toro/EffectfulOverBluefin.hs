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

data HandleOf (f :: Type -> Type) (ε :: B.Effects) = UnsafeHandleOf (forall x. f x -> IO x)

unsafeHandleOf :: (forall x. f x -> B.Eff ε' x) -> HandleOf f ε
unsafeHandleOf f = UnsafeHandleOf (B.unsafeUnEff . f)

_B_interpret ::
  (forall x. f x -> B.Eff ε' x) ->
  (forall ε. HandleOf f ε -> B.Eff (ε B.:& ε') a) ->
  B.Eff ε' a
_B_interpret g m = B.unsafeRemoveEff (m (unsafeHandleOf g))
-- The scope ε is contained in ε' so it's safe to transfer g from ε' to ε

interpret ::
  (forall x. f x -> Eff es x) ->
  Eff (HandleOf f ': es) a ->
  Eff es a
interpret g (Eff m) = Eff (\env ->
  _B_interpret (\f -> unEff (g f) env) (\h -> m (h :. env)))

type HEffect = (Type -> Type) -> (Type -> Type)

type HHandler f es = forall es0.
  (forall y. Eff es0 y -> Eff es y) ->
  forall x. f (Eff es0) x -> Eff es x

data HHandleOf (f :: HEffect) (ε :: B.Effects) where
  UnsafeHHandleOf :: (forall es0 x. f (Eff es0) x -> Eff es0 x) -> HHandleOf f ε

type B_HHandler f ε = forall ε0.
  (forall y. B.Eff ε0 y -> B.Eff ε y) ->
  forall x. f (B.Eff ε0) x -> B.Eff ε x

data B_HHandleOf (f :: HEffect) (ε :: B.Effects) where
  B_UnsafeHHandleOf :: (forall ε0 x. f (B.Eff ε0) x -> B.Eff ε0 x) -> B_HHandleOf f ε

_B_hinterpret ::
  B_HHandler f ε ->
  (forall ε'. B_HHandleOf f ε' -> B.Eff (ε' B.:& ε) a) ->
  B.Eff ε a
_B_hinterpret g m = B.unsafeRemoveEff (m (B_UnsafeHHandleOf ((B.UnsafeMkEff . B.unsafeUnEff) . g (B.UnsafeMkEff . B.unsafeUnEff))))
-- g can only be instantiated with an ε0 that contains ε

type B_HHandler' f ε = forall ε0.
  (forall y. B.Eff ε y -> B.Eff ε0 y) ->
  forall x. f (B.Eff ε0) x -> B.Eff ε0 x

data B_HHandleOf' (f :: HEffect) (ε :: B.Effects) where
  B_UnsafeHHandleOf' :: (forall ε0 x. f (B.Eff ε0) x -> B.Eff ε0 x) -> B_HHandleOf' f ε

_B_hinterpret' ::
  B_HHandler' f ε ->
  (forall ε'. B_HHandleOf' f ε' -> B.Eff (ε' B.:& ε) a) ->
  B.Eff ε a
_B_hinterpret' g m = B.unsafeRemoveEff (m (B_UnsafeHHandleOf' (g (B.UnsafeMkEff . B.unsafeUnEff))))


hinterpret ::
  HHandler f es ->
  Eff (HHandleOf f ': es) a ->
  Eff es a
hinterpret g (Eff m) = Eff (\env ->
  B.unsafeRemoveEff (m (
       UnsafeHHandleOf (\f -> Eff (\env0 -> unEff (g (unliftEff env0) f) (unsafeCoerce env)))
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
