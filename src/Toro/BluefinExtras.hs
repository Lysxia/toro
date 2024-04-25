{-# LANGUAGE
  GADTs,
  DataKinds,
  KindSignatures,
  RankNTypes,
  TypeOperators #-}
module Toro.BluefinExtras where

import Data.Kind (Type)
import qualified Bluefin.Eff as B
import qualified Bluefin.Internal as B (Eff(UnsafeMkEff,unsafeUnEff), unsafeRemoveEff)

data HandleOf (f :: Type -> Type) (ε :: B.Effects) = UnsafeHandleOf (forall x. f x -> IO x)

unsafeHandleOf :: (forall x. f x -> B.Eff ε' x) -> HandleOf f ε
unsafeHandleOf f = UnsafeHandleOf (B.unsafeUnEff . f)

interpret ::
  (forall x. f x -> B.Eff ε' x) ->
  (forall ε. HandleOf f ε -> B.Eff (ε B.:& ε') a) ->
  B.Eff ε' a
interpret g m = B.unsafeRemoveEff (m (unsafeHandleOf g))
-- The scope ε is contained in ε' so it's safe to transfer g from ε' to ε

type HEffect = (Type -> Type) -> (Type -> Type)

type HHandler f ε = forall ε0.
  (forall y. B.Eff ε0 y -> B.Eff ε y) ->
  forall x. f (B.Eff ε0) x -> B.Eff ε x

data HHandleOf (f :: HEffect) (ε :: B.Effects) where
  UnsafeHHandleOf :: (forall ε0 x. f (B.Eff ε0) x -> B.Eff ε0 x) -> HHandleOf f ε

type HHandler' f ε = forall ε0.
  (forall y. B.Eff ε y -> B.Eff ε0 y) ->
  forall x. f (B.Eff ε0) x -> B.Eff ε0 x

data HHandleOf' (f :: HEffect) (ε :: B.Effects) where
  UnsafeHHandleOf' :: (forall ε0 x. f (B.Eff ε0) x -> B.Eff ε0 x) -> HHandleOf' f ε

hinterpret ::
  HHandler f ε ->
  (forall ε'. HHandleOf f ε' -> B.Eff (ε' B.:& ε) a) ->
  B.Eff ε a
hinterpret g m = B.unsafeRemoveEff (m (UnsafeHHandleOf ((B.UnsafeMkEff . B.unsafeUnEff) . g (B.UnsafeMkEff . B.unsafeUnEff))))
-- g can only be instantiated with an ε0 that contains ε

hinterpret' ::
  HHandler' f ε ->
  (forall ε'. HHandleOf' f ε' -> B.Eff (ε' B.:& ε) a) ->
  B.Eff ε a
hinterpret' g m = B.unsafeRemoveEff (m (UnsafeHHandleOf' (g (B.UnsafeMkEff . B.unsafeUnEff))))
