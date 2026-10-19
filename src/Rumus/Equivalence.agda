{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Equivalence {A : Set} (_≟_ : DecidableEquality A) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true)
open import Data.List.Base using (List; _++_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Finite
open import Rumus.Support
import Rumus.Automaton
import Rumus.Worklist
import Rumus.Syntax

Distinguishes : Regex A → Regex A → List A → Set
Distinguishes r s x = ((x ∈ r) × (x ∈ s → ⊥)) ⊎ ((x ∈ s) × (x ∈ r → ⊥))

data Result (r s : Regex A) : Set where
  equivalent : r ≈ s → Result r s
  different : (x : List A) → Distinguishes r s x → Result r s

module Compare (r s : Regex A) where
  module Left = Rumus.Automaton _≟_ r
  module Right = Rumus.Automaton _≟_ s
  alphabet : List A
  alphabet = unique _≟_ (backwards (symbols r ++ symbols s))

  module Check = Rumus.Worklist Left.machine Right.machine alphabet

  same-language : Check.On (Left.initial , Right.initial) → r ≈ s
  same-language same {x} =
    (λ p → Right.accept-sound Right.initial x
      (proj₁ (same x (all-map (λ _ h → unique-cover _≟_ (backwards-cover (append-left (symbols s) h))) (support p)))
      (Left.accept-complete Left.initial x p))) ,
    (λ p → Left.accept-sound Left.initial x
      (proj₂ (same x (all-map (λ _ h → unique-cover _≟_ (backwards-cover (append-right (symbols r) h))) (support p)))
      (Right.accept-complete Right.initial x p)))

  result : Result r s
  result with Check.decide (Left.initial , Right.initial)
  ... | inj₁ same = equivalent (same-language same)
  ... | inj₂ (x , inj₁ (p , nq)) = different x (inj₁
    (Left.accept-sound Left.initial x p , (λ q → nq (Right.accept-complete Right.initial x q))))
  ... | inj₂ (x , inj₂ (q , np)) = different x (inj₂
    (Right.accept-sound Right.initial x q , (λ p → np (Left.accept-complete Left.initial x p))))

equivalence : (r s : Regex A) → Result r s
equivalence r s with Rumus.Syntax.equal _≟_ r s
... | yes refl = equivalent ≈-refl
... | no _ = Compare.result r s

witness-refutes : ∀ {r s x} → Distinguishes r s x → r ≈ s → ⊥
witness-refutes (inj₁ (p , n)) same = n (proj₁ same p)
witness-refutes (inj₂ (q , n)) same = n (proj₂ same q)

dec-equivalent : (r s : Regex A) → Dec (r ≈ s)
dec-equivalent r s with equivalence r s
... | equivalent proof = yes proof
... | different x proof = no (witness-refutes proof)

equivalent? : Regex A → Regex A → Bool
equivalent? r s = does (dec-equivalent r s)

equivalence-sound : ∀ r s → equivalent? r s ≡ true → r ≈ s
equivalence-sound r s with dec-equivalent r s
... | yes proof = λ _ → proof
... | no _ = λ ()

equivalence-complete : ∀ r s → r ≈ s → equivalent? r s ≡ true
equivalence-complete r s proof with dec-equivalent r s
... | yes _ = refl
... | no refute = ⊥-elim (refute proof)
