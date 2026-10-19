{-# OPTIONS --safe --without-K #-}

module Rumus.Machine where

open import Data.Bool.Base using (Bool; true)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Rumus.Finite using (_∈ˡ_)

record Machine (A : Set) : Set₁ where
  field
    State : Set
    equal : DecidableEquality State
    states : List State
    complete : ∀ q → q ∈ˡ states
    step : State → A → State
    output : State → Bool

open Machine public

run : ∀ {A} (m : Machine A) → State m → List A → State m
run m q [] = q
run m q (a ∷ x) = run m (step m q a) x

Accept : ∀ {A} (m : Machine A) → State m → List A → Set
Accept m q x = output m (run m q x) ≡ true

Equivalent : ∀ {A} (m : Machine A) → State m → State m → Set
Equivalent m p q = ∀ x → (Accept m p x → Accept m q x) × (Accept m q x → Accept m p x)
