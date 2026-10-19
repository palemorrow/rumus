{-# OPTIONS --safe --without-K --erasure --erased-matches #-}

open import Rumus.Machine using (Machine)
open import Data.List.Base using (List)

module Rumus.Worklist {A : Set} (m n : Machine A) (alphabet : List A) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using ([]; _∷_; _++_; map; length)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (_<_)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (yes; no)
open import Rumus.Finite
open import Rumus.Bisimulation m n alphabet public
  using (Pair; pair-equal; universe; universe-complete; successor; Good; Witness; prefix; observe; Closed; On; bisimilar)

Known : List Pair → List Pair → Pair → Set
Known seen pending q = (q ∈ˡ seen) ⊎ (q ∈ˡ pending)

Frontier : List Pair → List Pair → Set
Frontier seen pending = ∀ q → q ∈ˡ seen → Good q ×
  (∀ a → a ∈ˡ alphabet → Known seen pending (successor q a))

Cover : List Pair → List Pair → Set
Cover seen remaining = ∀ q → (q ∈ˡ seen) ⊎ (q ∈ˡ remaining)

skip-known : ∀ {seen pending q} → q ∈ˡ seen → ∀ {p} →
  Known seen (q ∷ pending) p → Known seen pending p
skip-known present (inj₁ p) = inj₁ p
skip-known present (inj₂ (here refl)) = inj₁ present
skip-known present (inj₂ (there p)) = inj₂ p

add-known : ∀ {seen pending q} extra {p} →
  Known seen (q ∷ pending) p → Known (q ∷ seen) (pending ++ extra) p
add-known extra (inj₁ p) = inj₁ (there p)
add-known extra (inj₂ (here refl)) = inj₁ (here refl)
add-known extra (inj₂ (there p)) = inj₂ (append-left extra p)

add-cover : ∀ {seen remaining} q → Cover seen remaining →
  Cover (q ∷ seen) (remove pair-equal q remaining)
add-cover q cover p with pair-equal p q
... | yes refl = inj₁ (here refl)
... | no neq with cover p
...   | inj₁ h = inj₁ (there h)
...   | inj₂ h = inj₂ (remove-preserve pair-equal q _ neq h)

all-append : ∀ {X : Set} {P : X → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
all-append [] q = q
all-append (p ∷ ps) q = p ∷ all-append ps q

map-paths : ∀ start q → (Witness q → Witness start) →
  (symbols : List A) → All (λ p → Witness p → Witness start) (map (successor q) symbols)
map-paths start q lift [] = []
map-paths start q lift (a ∷ symbols) = (λ w → lift (prefix q a w)) ∷ map-paths start q lift symbols

search : (start : Pair) → (@0 remaining : List Pair) →
  @0 Acc _<_ (length remaining) → (seen pending : List Pair) →
  @0 Cover seen remaining →
  All (λ q → Witness q → Witness start) pending →
  Frontier seen pending → Known seen pending start → On start ⊎ Witness start
search start remaining (acc smaller) seen pending cover paths frontier initial = walk pending paths frontier initial
  where
  walk : (pending : List Pair) → All (λ q → Witness q → Witness start) pending →
    Frontier seen pending → Known seen pending start → On start ⊎ Witness start
  walk [] [] frontier (inj₁ present) =
    inj₁ (bisimilar seen (λ q h → proj₁ (frontier q h) , λ a k → only-seen (proj₂ (frontier q h) a k)) start present)
    where
    only-seen : ∀ {q} → Known seen [] q → q ∈ˡ seen
    only-seen (inj₁ h) = h
    only-seen (inj₂ ())
  walk [] [] frontier (inj₂ ())
  walk (q ∷ pending) (lift ∷ paths) frontier initial with member pair-equal q seen
  ... | yes present = walk pending paths
    (λ p h → proj₁ (frontier p h) , λ a k → skip-known present (proj₂ (frontier p h) a k))
    (skip-known present initial)
  ... | no absent with observe q
  ...   | inj₂ w = inj₂ (lift w)
  ...   | inj₁ good = search start (remove pair-equal q remaining)
    (smaller (remove-shorter pair-equal q remaining remaining-member))
    (q ∷ seen) (pending ++ map (successor q) alphabet) (add-cover q cover)
    (all-append paths (map-paths start q lift alphabet)) new-frontier
    (add-known (map (successor q) alphabet) initial)
    where
    @0 remaining-member : q ∈ˡ remaining
    remaining-member with cover q
    ... | inj₁ h = ⊥-elim (absent h)
    ... | inj₂ h = h

    new-frontier : Frontier (q ∷ seen) (pending ++ map (successor q) alphabet)
    new-frontier p (here refl) = good , λ a h → inj₂
      (append-right pending (map-member (successor q) h))
    new-frontier p (there h) = proj₁ (frontier p h) , λ a k →
      add-known (map (successor q) alphabet) (proj₂ (frontier p h) a k)

decide : ∀ start → On start ⊎ Witness start
decide start = search start universe (<-wellFounded (length universe)) [] (start ∷ [])
  (λ q → inj₂ (universe-complete q)) ((λ w → w) ∷ []) (λ q ()) (inj₂ (here refl))
