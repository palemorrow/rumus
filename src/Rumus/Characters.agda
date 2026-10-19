{-# OPTIONS --safe --without-K #-}

module Rumus.Characters where

open import Data.Char.Base using (Char; toℕ)
open import Data.Char.Properties using (_≟_; toℕ-injective)
open import Data.Product.Base using (_,_)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Normalize _≟_ toℕ (toℕ-injective _ _) public using (normalize; normalize-correct)
open import Rumus.Normalize.Properties _≟_ toℕ (toℕ-injective _ _) public
  using (Canonical; normalize-idempotent; normalize-ordered; normalize-union-associative; normalize-union-commutative)
open import Rumus.NormalizedMatch _≟_ toℕ (toℕ-injective _ _) public using (match; accepts; sound; complete; step)
open import Rumus.Compiled _≟_ public
  using (Compiled; compile; compiled-match; compiled-accepts; compiled-sound; compiled-complete; start; advance; finish)
import Rumus.Equivalence _≟_ as E
open E public using (Result; equivalent; different; Distinguishes; witness-refutes; Minimal; minimal-length-bound; ShortestResult; proved-equivalent; shortest-difference)

shortest-equivalence : (r s : Regex Char) → ShortestResult r s
shortest-equivalence r s with E.shortest-equivalence (normalize r) (normalize s)
... | proved-equivalent same = proved-equivalent
  (≈-trans (≈-sym (normalize-correct r)) (≈-trans same (normalize-correct s)))
... | shortest-difference x proof minimal = shortest-difference x
  (E.transport-difference (normalize-correct r) (normalize-correct s) proof)
  (λ y h → minimal y (E.transport-difference (≈-sym (normalize-correct r)) (≈-sym (normalize-correct s)) h))

equivalence : (r s : Regex Char) → Result r s
equivalence r s = E.forget-shortest (shortest-equivalence r s)

dec-equivalent : (r s : Regex Char) → Dec (r ≈ s)
dec-equivalent r s with equivalence r s
... | equivalent same = yes same
... | different x witness = no (witness-refutes witness)
