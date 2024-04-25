{-# LANGUAGE
  BangPatterns,
  GADTs,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators #-}
module Toro.BluefinHandler where

import Bluefin.Eff
import Toro.BluefinCont

type HandlerBody f ss a = (forall x. f x -> (x -> Eff ss a) -> Eff ss a)

data Handler f s where
  Handler :: !(Prompt ss a s) -> HandlerBody f ss a -> Handler f s

handle ::
  HandlerBody f ss a ->
  (forall s. Handler f s -> Eff (s :& ss) a) ->
  Eff ss a
handle h act =
  prompt (\p -> act (Handler p h))

call :: Handler f s -> f b -> Eff ss b
call (Handler p h) op =
  control0 p (\k -> h op (k . pure))
