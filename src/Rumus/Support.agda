{-# OPTIONS --safe --without-K #-}

module Rumus.Support where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Finite

symbols : ∀ {A} → Regex A → List A
symbols ∅ = []
symbols ε = []
symbols (lit a) = a ∷ []
symbols (r ∪ s) = symbols r ++ symbols s
symbols (r ∙ s) = symbols r ++ symbols s
symbols (star r) = symbols r

all-map : ∀ {A : Set} {P Q : A → Set} {x} →
  (∀ a → P a → Q a) → All P x → All Q x
all-map f [] = []
all-map f (p ∷ ps) = f _ p ∷ all-map f ps

all-append : ∀ {A : Set} {P : A → Set} {x y} → All P x → All P y → All P (x ++ y)
all-append [] qs = qs
all-append (p ∷ ps) qs = p ∷ all-append ps qs

support : ∀ {A} {r : Regex A} {x} → x ∈ r → All (λ a → a ∈ˡ symbols r) x
support empty = []
support literal = here refl ∷ []
support (left {s = s} p) = all-map (λ _ → append-left (symbols s)) (support p)
support (right {r = r} p) = all-map (λ _ → append-right (symbols r)) (support p)
support (concat {r = r} {s} p q) = all-append
  (all-map (λ _ → append-left (symbols s)) (support p))
  (all-map (λ _ → append-right (symbols r)) (support q))
support stop = []
support (repeat p q) = all-append (support p) (support q)
