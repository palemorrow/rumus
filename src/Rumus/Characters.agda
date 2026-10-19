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
open import Rumus.NormalizedMatch _≟_ toℕ (toℕ-injective _ _) public using (match; accepts; sound; complete; step)
import Rumus.Equivalence _≟_ as E
open E public using (Result; equivalent; different; Distinguishes; witness-refutes)

equivalence : (r s : Regex Char) → Result r s
equivalence r s with E.equivalence (normalize r) (normalize s)
... | equivalent same = equivalent (≈-trans (≈-sym (normalize-correct r)) (≈-trans same (normalize-correct s)))
... | different x (inj₁ (p , nq)) = different x (inj₁
  (proj₁ (normalize-correct r) p , (λ q → nq (proj₂ (normalize-correct s) q))))
... | different x (inj₂ (q , np)) = different x (inj₂
  (proj₁ (normalize-correct s) q , (λ p → np (proj₂ (normalize-correct r) p))))

dec-equivalent : (r s : Regex Char) → Dec (r ≈ s)
dec-equivalent r s with equivalence r s
... | equivalent same = yes same
... | different x witness = no (witness-refutes witness)
