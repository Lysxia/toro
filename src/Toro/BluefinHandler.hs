{-# LANGUAGE
  BangPatterns,
  GADTs,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators #-}

-- * Algebraic effects and named handlers
--
-- Algebraic effect handlers are a powerful framework for
-- user-defined effects with a simple equational intuition.
--
-- An "algebraic effect" is a signature for a set of operations which we
-- represent with a GADT. For example, the "state effect" @State s@ contains
-- two operations: @Get@ takes no parameter and returns a value of type @s@,
-- and @Put@ takes a value of type @s@ and returns @()@. The constructors
-- @Get@ and @Put@ are "uninterpreted operations": they only describe the types
-- of arguments and results, with no further intrinsic meaning.
--
-- @
-- data State s r where
--   Get :: State s s
--   Put :: s -> State s ()
-- @
--
-- Below is an example of a stateful computation: a term of some type @'Eff' ss a@ with
-- a state handler @h :: 'Handler' (State s) z@ in scope (@z :> zz@).
-- The @State@ operations can be called using 'call' and the state handler @h@.
--
-- @
-- -- Increment a counter and return its previous value.
-- incr :: s :> ss => Handler (State Int) s -> Eff ss Int
-- incr h = do
--     n <- get
--     put (n + 1)
--     pure n
--   where
--     get = call h Get
--     put s = call h (Put s)
-- @
--
-- We handle the state effect by giving an interpretation of the @Get@ and @Put@
-- operations, as a function @f :: 'HandlerBody' (State s) ss a@.
--
-- To 'call' @Get@ or @Put@ is to call the function @f@ supplied by 'handle'.
-- The following equations show how 'handle' propagates an interpretation
-- @f@ throughout a computation that calls @Get@ and @Put@:
--
-- @
-- handle f (\\h -> call h Get     >>= k h) = f Get     (handle f (\\h -> k h))
-- handle f (\\h -> call h (Put s) >>= k h) = f (Put s) (handle f (\\h -> k h))
-- handle f (\\h -> pure r) = pure r
-- @
--
-- For example, @'handle' f@ maps the above @incr@ computation to:
--
-- @
-- handle f incr =
--   f Get \\n ->
--   f (Put (n+1)) \\() ->
--   pure n
-- @
module Toro.BluefinHandler
  ( AEffect
  , HandlerBody
  , Handler
  , handle
  , call
  ) where

import Data.Kind (Type)
import Bluefin.Eff
import Toro.BluefinCont

-- | Algebraic effect.
type AEffect = Type -> Type

-- | Interpretation of an algebraic effect @f@: a function to handle the operations of @f@.
type HandlerBody :: AEffect -> Effects -> Type -> Type
type HandlerBody f ss a = (forall x. f x -> (x -> Eff ss a) -> Eff ss a)

-- | Handler to call operations of the effect @f@.
type Handler :: AEffect -> Effects -> Type
data Handler f s where
  Handler :: !(PromptTag ss a s) -> HandlerBody f ss a -> Handler f s

-- | Handle operations of @f@.
handle ::
  HandlerBody f ss a ->
  (forall s. Handler f s -> Eff (s :& ss) a) ->
  Eff ss a
handle h act =
  prompt (\p -> act (Handler p h))

-- | Call an operation of @f@.
call :: Handler f s -> f b -> Eff ss b
call (Handler p h) op =
  control p (\k -> h op (k . pure))
