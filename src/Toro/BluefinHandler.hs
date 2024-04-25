{-# LANGUAGE
  BangPatterns,
  GADTs,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators #-}

-- | = Algebraic effects and named handlers
--
-- Algebraic effect handlers are a powerful framework for
-- user-defined effects with a simple equational intuition.
--
-- An "algebraic effect" is a signature for a set of operations which we
-- represent with a GADT. For example, the "state effect" @State s@ contains
-- two operations: @Get@ takes no parameter and returns a value of type @s@,
-- and @Put@ takes a value of type @s@ and returns @()@. The constructors
-- @Get@ and @Put@ are "uninterpreted operations": they only describe the types
-- of arguments and results, with no intrinsic meaning.
-- 
-- @
-- data State s r where
--   Get :: State s s
--   Put :: s -> State s ()
-- @
--
-- Below is an example of a stateful computation: a term of some type @'Eff' zz a@ with
-- a state handler @h :: 'Handler' (State s) z@ in scope (@z :> zz@).
-- The @State@ operations can be called using 'call' and the state handler @h@.
--
-- @
-- -- Increment a counter and return its previous value.
-- incr :: z :> zz => Handler (State Int) z -> Eff zz Int
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
-- operations, as a function @f :: 'HandlerBody' (State s) zz a@.
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
-- With those equations, @'handle' f@ applied to the above @incr@ simplifies to:
--
-- @
-- 'handle' f incr =
--   f Get \\n ->
--   f (Put (n+1)) \\() ->
--   pure n
-- @
--
-- === References
--
-- - <https://www.microsoft.com/en-us/research/uploads/prod/2021/05/namedh-tr.pdf First-class names for effect handlers> (2021) by Ningning Xie, Youyou Cong, and Daan Leijen.
module Toro.BluefinHandler
  ( AEffect

    -- * Simple continuations
  , HandlerBody
  , Handler
  , handle
  , call

    -- * Cancellable continuations
  , HandlerBody'
  , Handler'
  , handle'
  , call'
  , continue
  , discontinue
  , discontinueIO
  ) where

import Control.Exception (Exception)
import Data.Kind (Type)
import Bluefin.Eff
import Bluefin.IO (IOE)
import Toro.BluefinCont
import Toro.BluefinExceptionDynamic

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
--
-- === Warning for exception-like effects
--
-- If the handler might not call the continuation (like for an exception effect), and
-- if the handled computation manages resources (e.g., opening files, transactions)
-- prefer 'handle'' to trigger resource clean up with cancellable continuations.
handle ::
  HandlerBody f ss a ->
  (forall s. Handler f s -> Eff (s :& ss) a) ->
  Eff ss a
handle h act = reset (\p -> act (Handler p h))

-- | Call an operation of @f@.
call :: s :> ss => Handler f s -> f a -> Eff ss a
call (Handler p h) op = shift0 p (\k -> h op (continue k))

-- | Variant of 'handle' with cancellable continuations.
--
-- This is useful to work with native exception handlers such as
-- 'Control.Exception.bracket' and other resource-management schemes à la
-- @resourcet@.
--
-- === Linearity
--
-- The continuation should be called exactly once (via 'continue' or 'discontinue')
-- to avoid use-after-free errors.
-- Enforcing this requirement with linear types would be a welcome contribution.
--
-- === Example
--
-- Given @bracket@ function (hypothetically adapted to bluefin) and a @Fail@ effect,
-- the simple 'handle' may cause resource leaks:
--
-- @
-- 'handle' (\\_e _k -> pure Nothing)
--   (bracket acquire release (\\_ -> call h Fail))
-- @
--
-- @bracket@ is intended to ensure that the acquired resource is released even if the bracketed
-- function throws an exception. However, when the @Fail@ operation is called, the handler
-- @(\_e _k -> pure Nothing)@ discards the continuation @_k@ which contains the
-- exception handler installed by @bracket@.
-- The resource leaks because @release@ will never be called.
--
-- The more general 'handle'' lets us cancel the continuation with 'discontinue'.
-- Cancellable continuations require an 'IOE' handle.
--
-- @
-- data CancelContinuation = CancelContinuation
--   deriving (Show, Exception)
--
-- 'handle'' io (\\_e k -> try @CancelContinuation ('discontinueIO' k CancelContinuation) >> pure Nothing)
--   (bracket acquire release (\\_ -> call h Fail))
-- @
handle' :: ex :> ss =>
  h ex ->
  HandlerBody' ex f ss a ->
  (forall s. Handler' ex f s -> Eff (s :& ss) a) ->
  Eff ss a
handle' _ h act = reset (\p -> act (Handler' p h))

-- | Variant of 'HandlerBody' with cancellable continuations (see 'handle'').
type HandlerBody' :: Effects -> AEffect -> Effects -> Type -> Type
type HandlerBody' ex f ss a = (forall x ss0. ex :> ss0 => f x -> (Eff ss0 x -> Eff ss a) -> Eff ss a)

-- | Variant of 'Handler' with cancellable continuations (see 'handle'').
type Handler' :: Effects -> AEffect -> Effects -> Type
data Handler' ex f s where
  Handler' :: !(PromptTag ss a s) -> HandlerBody' ex f ss a -> Handler' ex f s

-- | Variant of 'call' with cancellable continuations (see 'handle'').
call' :: (ex :> es, s :> es) => Handler' ex f s -> f a -> Eff es a
call' (Handler' p h) op = shift0 p (\k -> h op k)

-- | Resume a cancellable continuation with a result.
--
-- In other words, this converts a cancellable continuation to a simple continuation.
continue :: (Eff ss0 b -> Eff ss a) -> b -> Eff ss a
continue k = k . pure

-- | Cancel a continuation: resume by throwing a (dynamic) exception.
discontinue :: (Exception e, ex :> es0) => DynExn ex -> (Eff es0 b -> Eff es a) -> e -> Eff es a
discontinue ex k e = k (throw ex e)

-- | 'discontinue' with an 'IOE' handle instead of the more restrictive 'DynExn'.
discontinueIO :: (Exception e, io :> es0) => IOE io -> (Eff es0 b -> Eff es a) -> e -> Eff es a
discontinueIO io = discontinue (ioeToDynExn io)
