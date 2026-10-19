{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
import Rumus.Regex

module Rumus.Automaton {A : Set} (_≟_ : DecidableEquality A) (r : Rumus.Regex.Regex A) where

open import Data.Bool.Base using (true)
open import Data.List.Base using (List; []; _∷_; _++_; map; concatMap)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (yes; no; does)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Algebra
open import Rumus.Nullable
open import Rumus.Derivative _≟_
open import Rumus.Match _≟_ using (sound; complete)
open import Rumus.Join
open import Rumus.Finite
open import Rumus.Residual _≟_
open import Rumus.Machine hiding (State; complete; equal; states; step; output)

data State : Set where
  initial : State
  residual : Selection (positions r) → State

equal : DecidableEquality State
equal initial initial = yes refl
equal initial (residual _) = no (λ ())
equal (residual _) initial = no (λ ())
equal (residual p) (residual q) with selection-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }

states : List State
states = initial ∷ map residual (selections (positions r))

states-complete : ∀ q → q ∈ˡ states
states-complete initial = here refl
states-complete (residual q) = there (map-member residual (selections-complete q))

denote : State → Regex A
denote initial = r
denote (residual q) = join body (selected q)

step : State → A → State
step initial a = residual (select position-equal (positions r) (first r a))
step (residual q) a = residual (select position-equal (positions r) (concatMap (λ p → next p a) (selected q)))

join-next-correct : ∀ (ps : List (Position r)) a → join body (concatMap (λ p → next p a) ps) ≈ derive a (join body ps)
join-next-correct [] a = ≈-refl
join-next-correct (p ∷ ps) a = ≈-trans (join-append body (next p a) (concatMap (λ q → next q a) ps))
  (union-cong (next-correct p a) (join-next-correct ps a))

step-correct : ∀ q a → denote (step q a) ≈ derive a (denote q)
step-correct initial a = ≈-trans
  (selection-correct position-equal body (positions r) positions-complete (first r a)) (first-correct r a)
step-correct (residual q) a = ≈-trans
  (selection-correct position-equal body (positions r) positions-complete (concatMap (λ p → next p a) (selected q)))
  (join-next-correct (selected q) a)

machine : Machine A
machine = record
  { State = State
  ; equal = equal
  ; states = states
  ; complete = states-complete
  ; step = step
  ; output = λ q → does (nullable (denote q))
  }

accept-sound : ∀ q x → Accept machine q x → x ∈ denote q
accept-sound q [] p = sound (denote q) [] p
accept-sound q (a ∷ x) p = derive-sound (denote q) a (proj₁ (step-correct q a) (accept-sound (step q a) x p))

accept-complete : ∀ q x → x ∈ denote q → Accept machine q x
accept-complete q [] p = complete (denote q) [] p
accept-complete q (a ∷ x) p = accept-complete (step q a) x (proj₂ (step-correct q a) (derive-complete (denote q) a p))
