{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Equivalence {A : Set} (_≟_ : DecidableEquality A) where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool.Base using (Bool; true)
open import Data.List.Base using (List; _++_; length)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no; does)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Data.Nat.Base using (_≤_)
open import Data.List.Relation.Unary.All using (All)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Finite
open import Rumus.Support
import Rumus.CachedAutomaton
import Rumus.BreadthFirst
import Rumus.Syntax

Distinguishes : Regex A → Regex A → List A → Set
Distinguishes r s x = ((x ∈ r) × (x ∈ s → ⊥)) ⊎ ((x ∈ s) × (x ∈ r → ⊥))

data Result (r s : Regex A) : Set where
  equivalent : r ≈ s → Result r s
  different : (x : List A) → Distinguishes r s x → Result r s

Minimal : Regex A → Regex A → List A → Set
Minimal r s x = ∀ y → Distinguishes r s y → length x ≤ length y

data ShortestResult (r s : Regex A) : Set where
  proved-equivalent : r ≈ s → ShortestResult r s
  shortest-difference : (x : List A) → Distinguishes r s x → Minimal r s x → ShortestResult r s

forget-shortest : ∀ {r s} → ShortestResult r s → Result r s
forget-shortest (proved-equivalent proof) = equivalent proof
forget-shortest (shortest-difference x proof minimal) = different x proof

transport-difference : ∀ {r s t u x} → r ≈ t → s ≈ u → Distinguishes r s x → Distinguishes t u x
transport-difference rt su (inj₁ (p , nq)) = inj₁ (proj₁ rt p , λ q → nq (proj₂ su q))
transport-difference rt su (inj₂ (q , np)) = inj₂ (proj₁ su q , λ p → np (proj₂ rt p))

module Compare (r s : Regex A) where
  module Left = Rumus.CachedAutomaton _≟_ r
  module Right = Rumus.CachedAutomaton _≟_ s
  alphabet : List A
  alphabet = unique _≟_ (backwards (symbols r ++ symbols s))

  module Check = Rumus.BreadthFirst Left.machine Right.machine alphabet

  same-language : Check.On (Left.initial , Right.initial) → r ≈ s
  same-language same {x} =
    (λ p → Right.accept-sound Right.initial x
      (proj₁ (same x (all-map (λ _ h → unique-cover _≟_ (backwards-cover (append-left (symbols s) h))) (support p)))
      (Left.accept-complete Left.initial x p))) ,
    (λ p → Left.accept-sound Left.initial x
      (proj₂ (same x (all-map (λ _ h → unique-cover _≟_ (backwards-cover (append-right (symbols r) h))) (support p)))
      (Right.accept-complete Right.initial x p)))

  witness-sound : ∀ {x} → Check.Separates (Left.initial , Right.initial) x → Distinguishes r s x
  witness-sound (inj₁ (p , nq)) = inj₁
    (Left.accept-sound Left.initial _ p , λ q → nq (Right.accept-complete Right.initial _ q))
  witness-sound (inj₂ (q , np)) = inj₂
    (Right.accept-sound Right.initial _ q , λ p → np (Left.accept-complete Left.initial _ p))

  witness-complete : ∀ {x} → Distinguishes r s x → Check.Separates (Left.initial , Right.initial) x
  witness-complete (inj₁ (p , nq)) = inj₁
    (Left.accept-complete Left.initial _ p , λ q → nq (Right.accept-sound Right.initial _ q))
  witness-complete (inj₂ (q , np)) = inj₂
    (Right.accept-complete Right.initial _ q , λ p → np (Left.accept-sound Left.initial _ p))

  witness-support : ∀ {x} → Distinguishes r s x → All (λ a → a ∈ˡ alphabet) x
  witness-support (inj₁ (p , _)) = all-map
    (λ _ h → unique-cover _≟_ (backwards-cover (append-left (symbols s) h))) (support p)
  witness-support (inj₂ (q , _)) = all-map
    (λ _ h → unique-cover _≟_ (backwards-cover (append-right (symbols r) h))) (support q)

  shortest-result : ShortestResult r s
  shortest-result with Check.decide (Left.initial , Right.initial)
  ... | inj₁ same = proved-equivalent (same-language same)
  ... | inj₂ proof = shortest-difference (Check.Shortest.word proof)
    (witness-sound (Check.Shortest.witness proof))
    (λ y h → Check.Shortest.minimal proof y (witness-support h) (witness-complete h))

shortest-equivalence : (r s : Regex A) → ShortestResult r s
shortest-equivalence r s with Rumus.Syntax.equal _≟_ r s
... | yes refl = proved-equivalent ≈-refl
... | no _ = Compare.shortest-result r s

equivalence : (r s : Regex A) → Result r s
equivalence r s = forget-shortest (shortest-equivalence r s)

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
