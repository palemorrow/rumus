{-# OPTIONS --safe --without-K #-}

module Rumus.Parser.Syntax where

open import Data.Char.Base using (Char)
open import Data.List.Base using (List)
open import Rumus.Regex

data Operator : Set where
  group choice sequence : Operator

Operands : Set
Operands = List (Regex Char)

Stack : Set
Stack = List Operator

atom : Char → Regex Char
atom '#' = ∅
atom '@' = ε
atom a = lit a
