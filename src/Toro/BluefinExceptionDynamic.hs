{-# LANGUAGE
  KindSignatures,
  ScopedTypeVariables,
  TypeOperators #-}
module Toro.BluefinExceptionDynamic
  ( DynExn
  , ioeToDynExn
  , throw
  , catch
  , bracket
  , finally
  , onException
  , throwIO
  , catchIO
  ) where

import qualified Control.Exception as E
import qualified Bluefin.Internal as B
import Bluefin.Eff
import Bluefin.IO

-- | Capability to throw dynamic exceptions.
data DynExn (ex :: Effects) = DynExn

-- | Refine an 'IOE' capability to a 'DynExn'.
ioeToDynExn :: IOE io -> DynExn io
ioeToDynExn _ = DynExn

throw :: (E.Exception e, ex :> es) => DynExn ex -> e -> Eff es a
throw _ e = B.UnsafeMkEff (E.throwIO e)

catch :: (E.Exception e, ex :> es) => DynExn ex -> Eff es a -> (e -> Eff es a) -> Eff es a
catch _ m h = B.UnsafeMkEff (E.catch (B.unsafeUnEff m) (B.unsafeUnEff . h))

bracket :: ex :> es => DynExn ex -> Eff es a -> (a -> Eff es ()) -> (a -> Eff es b) -> Eff es b
bracket ex acquire release run = do
  a <- acquire
  finally ex (run a) (release a)

finally :: ex :> es => DynExn ex -> Eff es a -> Eff es () -> Eff es a
finally ex run cleanup =
  onException ex run cleanup   -- if run throws an exception, then only this cleanup will run
    <* cleanup                 -- if run does not throw, then only this cleanup will run

onException :: ex :> es => DynExn ex -> Eff es a -> Eff es () -> Eff es a
onException ex run cleanup = catch ex run (\(e :: E.SomeException) -> cleanup >> throw ex e)

throwIO :: (E.Exception e, io :> es) => IOE io -> e -> Eff es a
throwIO io = throw (ioeToDynExn io)

catchIO :: (E.Exception e, io :> es) => IOE io -> Eff es a -> (e -> Eff es a) -> Eff es a
catchIO io = catch (ioeToDynExn io)
