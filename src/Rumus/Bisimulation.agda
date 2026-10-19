{-# OPTIONS --safe --without-K #-}

open import Rumus.Machine using (Machine)
open import Data.List.Base using (List)

module Rumus.Bisimulation {A : Set} (m n : Machine A) (alphabet : List A) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)
open import Relation.Nullary using (yes; no)
open import Rumus.Machine
open import Rumus.Finite

Pair : Set
Pair = State m × State n

pair-equal : DecidableEquality Pair
pair-equal (p , q) (s , t) with equal m p s | equal n q t
... | yes refl | yes refl = yes refl
... | no k | _ = no λ { refl → k refl }
... | _ | no k = no λ { refl → k refl }

universe : List Pair
universe = cartesian (states m) (states n)

universe-complete : ∀ q → q ∈ˡ universe
universe-complete (p , q) = cartesian-member (complete m p) (complete n q)

successor : Pair → A → Pair
successor (p , q) a = step m p a , step n q a

Good : Pair → Set
Good (p , q) = output m p ≡ output n q

Witness : Pair → Set
Witness (p , q) = Σ (List A) λ x →
  (Accept m p x × (Accept n q x → ⊥)) ⊎
  (Accept n q x × (Accept m p x → ⊥))

prefix : ∀ q a → Witness (successor q a) → Witness q
prefix q a (x , h) = (a ∷ x) , h

observe : ∀ q → Good q ⊎ Witness q
observe (p , q) with output m p in ep | output n q in eq
... | true | true = inj₁ refl
... | false | false = inj₁ refl
... | true | false = inj₂ ([] , inj₁ (ep , (λ h → false-true (trans (sym eq) h))))
  where
  false-true : false ≡ true → ⊥
  false-true ()
... | false | true = inj₂ ([] , inj₂ (eq , (λ h → false-true (trans (sym ep) h))))
  where
  false-true : false ≡ true → ⊥
  false-true ()

Outside : List Pair → Set
Outside remaining = ∀ q → (q ∈ˡ remaining → ⊥) → Witness q

Edges : List Pair → Pair → List A → Set
Edges remaining q symbols = ∀ a → a ∈ˡ symbols → successor q a ∈ˡ remaining

edges : ∀ remaining q symbols → Outside remaining → Edges remaining q symbols ⊎ Witness q
edges remaining q [] outside = inj₁ (λ a ())
edges remaining q (a ∷ symbols) outside with member pair-equal (successor q a) remaining
... | no absent = inj₂ (prefix q a (outside (successor q a) absent))
... | yes present with edges remaining q symbols outside
...   | inj₂ w = inj₂ w
...   | inj₁ rest = inj₁ λ { _ (here refl) → present ; b (there h) → rest b h }

Closed : List Pair → Set
Closed remaining = ∀ q → q ∈ˡ remaining → Good q × Edges remaining q alphabet

audit : ∀ remaining candidates → Outside remaining →
  (∀ q → q ∈ˡ candidates → Good q × Edges remaining q alphabet) ⊎
  (Σ Pair λ q → (q ∈ˡ candidates) × Witness q)
audit remaining [] outside = inj₁ (λ q ())
audit remaining (q ∷ qs) outside with observe q
... | inj₂ w = inj₂ (q , here refl , w)
... | inj₁ good with edges remaining q alphabet outside
...   | inj₂ w = inj₂ (q , here refl , w)
...   | inj₁ next with audit remaining qs outside
...     | inj₂ (p , h , w) = inj₂ (p , there h , w)
...     | inj₁ rest = inj₁ λ { _ (here refl) → good , next ; p (there h) → rest p h }

remove-outside : ∀ remaining q → Outside remaining → Witness q → Outside (remove pair-equal q remaining)
remove-outside remaining q outside witness p absent with pair-equal p q
... | yes refl = witness
... | no different = outside p (λ h → absent (remove-preserve pair-equal q remaining different h))

record Stable : Set where
  field
    relation : List Pair
    closed : Closed relation
    outside : Outside relation

refine : ∀ remaining → Acc _<_ (length remaining) → Outside remaining → Stable
refine remaining (acc smaller) outside with audit remaining remaining outside
... | inj₁ closed = record { relation = remaining ; closed = closed ; outside = outside }
... | inj₂ (q , present , witness) = refine (remove pair-equal q remaining)
  (smaller (remove-shorter pair-equal q remaining present)) (remove-outside remaining q outside witness)

stable : Stable
stable = refine universe (<-wellFounded (length universe)) (λ q absent → ⊥-elim (absent (universe-complete q)))

On : Pair → Set
On (p , q) = ∀ x → All (λ a → a ∈ˡ alphabet) x →
  (Accept m p x → Accept n q x) × (Accept n q x → Accept m p x)

bisimilar : ∀ remaining → Closed remaining → ∀ q → q ∈ˡ remaining → On q
bisimilar remaining closed (p , q) present [] [] =
  (λ h → trans (sym (proj₁ (closed (p , q) present))) h) ,
  (λ h → trans (proj₁ (closed (p , q) present)) h)
bisimilar remaining closed q present (a ∷ x) (h ∷ hs) =
  bisimilar remaining closed (successor q a) (proj₂ (closed q present) a h) x hs

decide : ∀ q → On q ⊎ Witness q
decide q with stable
... | record { relation = remaining ; closed = closed ; outside = outside } with member pair-equal q remaining
...   | yes present = inj₁ (bisimilar remaining closed q present)
...   | no absent = inj₂ (outside q absent)
