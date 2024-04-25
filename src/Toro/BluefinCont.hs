{-# LANGUAGE
  BangPatterns,
  MagicHash,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators,
  UnboxedTuples #-}

-- * Delimited continuations
--
-- A thin wrapper around GHC's
-- <native delimited continuations primitives https://ghc-proposals.readthedocs.io/en/latest/proposals/0313-delimited-continuation-primops.html>.
--
-- Those primitives let us manipulate slices of the call stack/evaluation
-- context delimited by prompts.
--
-- We use this module to implement algebraic effect handlers, which provide a more
-- structured interface for manipulating continuations.
--
-- The behavior of 'prompt' and 'control' is summarized by the following equations:
--
-- @
-- 'prompt' (\\_ -> 'pure' x) = 'pure' x
-- 'prompt' (\\t -> C ('control' t f)) = f (\\x -> 'prompt' (\\t -> C x))
-- @
--
-- where @C@ is an evaluation context (in which @t@ may occur),
-- a term of the following form:
--
-- > C x ::= C x >>= f      -- for any f
-- >       | H (\h -> C x)  -- for any bluefin handler H ∈ { prompt, (`runState` s), ... }
-- >       | x
module Toro.BluefinCont
  ( PromptTag
  , prompt
  , control
  ) where

import Data.Kind (Type)
import GHC.Exts (State#, RealWorld, PromptTag#, prompt#, control0#, newPromptTag#)
import GHC.IO (IO(IO))
import Bluefin.Internal (Eff(..))
import Bluefin.Eff

-- | Tag for a prompt of type @a@.
type PromptTag :: Effects -> Type -> Effects -> Type
data PromptTag ss a s = PromptTag (PromptTag# a)

unsafeMkEff :: (State# RealWorld -> (# State# RealWorld , a #)) -> Eff ss a
unsafeMkEff f = UnsafeMkEff (IO f)

unsafeRunEff :: Eff ss a -> State# RealWorld -> (# State# RealWorld , a #)
unsafeRunEff (UnsafeMkEff (IO f)) = f

-- | Push a tagged prompt of type @a@ on the stack and pass it to the tagged computation.
--
-- A prompt is a marker on the call stack (evaluation context).
-- Those markers delimit slices of the call stack which can be removed from the
-- stack with 'control'. Such a slice is copied as a value on the heap,
-- a continuation, which is a function of type @Eff ss b -> Eff ss0 b@.
-- Calling the continuation restores the slice on the stack.
prompt :: forall a ss.
  (forall s. PromptTag ss a s -> Eff (s :& ss) a) ->
  Eff ss a
prompt f = unsafeMkEff (\z0 -> case newPromptTag# z0 of
    (# z1, tag #) -> prompt# tag (unsafeRunEff (f (PromptTag tag))) z1)

-- | Capture the continuation up to the tagged prompt.
-- The prompt is reinserted on the stack when the continuation is called.
control :: forall s a b ss ss0.
  PromptTag ss0 a s ->
  ((Eff ss b -> Eff ss0 a) -> Eff ss0 a) ->
  Eff ss b
control (PromptTag tag) f = unsafeMkEff (\z0 ->
  control0# tag (\k# ->
    unsafeRunEff (f (unsafeMkEff . prompt# tag . k# . unsafeRunEff))) z0)
