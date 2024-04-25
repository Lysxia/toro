{-# LANGUAGE
  BangPatterns,
  GADTs,
  RankNTypes,
  ScopedTypeVariables,
  StandaloneKindSignatures,
  TypeOperators #-}
module Toro.BluefinLib where

import Bluefin.Eff
import Toro.BluefinHandler

data State s x where
  Get :: State s s
  Put :: s -> State s ()

runState :: forall s a zz.
  (forall z. Handler (State s) z -> Eff (z :& zz) a) ->
  s -> Eff zz (a, s)
runState f s0 = unwrap s0 (handle stateHandler (wrap . f))
  where
    stateHandler :: HandlerBody (State s) zz (s -> Eff zz (a, s))
    stateHandler Get k = pure (\s -> k s >>= \k1 -> k1 s)
    stateHandler (Put s) k = pure (\_ -> k () >>= \k1 -> k1 s)

    wrap :: Eff (z :& zz) a -> Eff (z :& zz) (s -> Eff zz (a, s))
    wrap = fmap (\a s -> pure (a, s))

    unwrap :: s -> Eff zz (s -> Eff zz b) -> Eff zz b
    unwrap s m = m >>= \k -> k s

get :: z :> zz => Handler (State s) z -> Eff zz s
get h = call h Get

put :: z :> zz => Handler (State s) z -> s -> Eff zz ()
put h s = call h (Put s)

data Error e x where
  Throw :: e -> Error e x

try :: forall e a zz.
  (forall z. Handler (Error e) z -> Eff (z :& zz) a) ->
  Eff zz (Either e a)
try f = handle errorHandler (fmap Right . f)
  where
    errorHandler :: HandlerBody (Error e) zz (Either e a)
    errorHandler (Throw e) _ = pure (Left e)

throw :: z :> zz => Handler (Error e) z -> e -> Eff zz a
throw h e = call h (Throw e)

data Coroutine i o a where
  Yield :: o -> Coroutine i o i

execCoroutine :: forall i o a zz.
  (o -> Eff zz i) ->
  (forall z. Handler (Coroutine i o) z -> Eff (z :& zz) a) ->
  Eff zz a
execCoroutine h f = handle coroutineHandler f
  where
    coroutineHandler :: HandlerBody (Coroutine i o) zz a
    coroutineHandler (Yield o) k = h o >>= k

evalCoroutine :: forall i o a zz.
  (forall z. Handler (Coroutine i o) z -> Eff (z :& zz) a) ->
  Pipe i o (Eff zz) a
evalCoroutine f = Pipe (handle coroutineHandler (wrap . f))
  where
    coroutineHandler :: HandlerBody (Coroutine i o) zz (PipeEvent i o (Eff zz) a)
    coroutineHandler (Yield o) k = pure (Yielding o k)

    wrap :: Eff (z :& zz) a -> Eff (z :& zz) (PipeEvent i o (Eff zz) a)
    wrap = fmap Done

data PipeEvent i o m a
  = Done a
  | Yielding o (i -> m (PipeEvent i o m a))

newtype Pipe i o m a = Pipe (m (PipeEvent i o m a))

