{-# OPTIONS --safe --without-K #-}

module Rumus.Regex where

infixr 5 _∪_
infixr 6 _∙_

data Regex (A : Set) : Set where
  ∅ ε : Regex A
  lit : A → Regex A
  _∪_ _∙_ : Regex A → Regex A → Regex A
  star : Regex A → Regex A
