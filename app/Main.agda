{-# OPTIONS --without-K #-}

module Main where

open import Data.Bool.Base using (true; false)
open import Data.Unit.Base using (⊤)
open import Agda.Builtin.Int using (pos)
open import IO.Primitive.Core using (IO; _>>=_)
open import IO.Primitive.Finite using (putStrLn)
open import System.Environment.Primitive using (getArgs)
open import System.Exit.Primitive using (exitWith; ExitFailure)
open import Rumus.Command

emit : Response → IO ⊤
emit (response true text) = putStrLn text
emit (response false text) = putStrLn text >>= λ _ → exitWith (ExitFailure (pos 1))

main : IO ⊤
main = getArgs >>= λ args → emit (command args)
