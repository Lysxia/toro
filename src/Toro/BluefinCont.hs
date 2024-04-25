{-# LANGUAGE
  BangPatterns,
  MagicHash,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators,
  UnboxedTuples #-}
module Toro.BluefinCont
  ( Prompt
  , prompt
  , control0
  ) where

import Data.Kind (Type)
import GHC.Exts (State#, RealWorld, PromptTag#, prompt#, control0#, newPromptTag#)
import GHC.IO (IO(IO))
import Bluefin.Internal (Eff(..))
import Bluefin.Eff

type Prompt :: Effects -> Type -> Effects -> Type
data Prompt ss a s = Prompt (PromptTag# a)

unsafeMkEff :: (State# RealWorld -> (# State# RealWorld , a #)) -> Eff ss a
unsafeMkEff f = UnsafeMkEff (IO f)

unsafeRunEff :: Eff ss a -> State# RealWorld -> (# State# RealWorld , a #)
unsafeRunEff (UnsafeMkEff (IO f)) = f

prompt :: forall a ss. (forall s. Prompt ss a s -> Eff (s :& ss) a) -> Eff ss a
prompt f = unsafeMkEff (\z0 -> case newPromptTag# z0 of
    (# z1, tag #) -> prompt# tag (unsafeRunEff (f (Prompt tag))) z1)

control0 :: forall s a b ss ss0. Prompt ss0 a s -> ((Eff ss b -> Eff ss0 a) -> Eff ss0 a) -> Eff ss b
control0 (Prompt tag) f = unsafeMkEff (\z0 ->
  control0# tag (\k# ->
    unsafeRunEff (f (unsafeMkEff . k# . unsafeRunEff))) z0)
