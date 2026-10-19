{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Syntax {A : Set} (_≟_ : DecidableEquality A) where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ)
open import Data.Bool.Base using (Bool; true; false)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (Dec; yes; no)
open import Rumus.Regex

equal : DecidableEquality (Regex A)
equal ∅ ∅ = yes refl
equal ε ε = yes refl
equal (lit a) (lit b) with a ≟ b
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
equal (r ∪ s) (t ∪ u) with equal r t | equal s u
... | yes refl | yes refl = yes refl
... | no n | _ = no λ { refl → n refl }
... | _ | no n = no λ { refl → n refl }
equal (r ∙ s) (t ∙ u) with equal r t | equal s u
... | yes refl | yes refl = yes refl
... | no n | _ = no λ { refl → n refl }
... | _ | no n = no λ { refl → n refl }
equal (star r) (star s) with equal r s
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
equal ∅ ε = no (λ ())
equal ∅ (lit _) = no (λ ())
equal ∅ (_ ∪ _) = no (λ ())
equal ∅ (_ ∙ _) = no (λ ())
equal ∅ (star _) = no (λ ())
equal ε ∅ = no (λ ())
equal ε (lit _) = no (λ ())
equal ε (_ ∪ _) = no (λ ())
equal ε (_ ∙ _) = no (λ ())
equal ε (star _) = no (λ ())
equal (lit _) ∅ = no (λ ())
equal (lit _) ε = no (λ ())
equal (lit _) (_ ∪ _) = no (λ ())
equal (lit _) (_ ∙ _) = no (λ ())
equal (lit _) (star _) = no (λ ())
equal (_ ∪ _) ∅ = no (λ ())
equal (_ ∪ _) ε = no (λ ())
equal (_ ∪ _) (lit _) = no (λ ())
equal (_ ∪ _) (_ ∙ _) = no (λ ())
equal (_ ∪ _) (star _) = no (λ ())
equal (_ ∙ _) ∅ = no (λ ())
equal (_ ∙ _) ε = no (λ ())
equal (_ ∙ _) (lit _) = no (λ ())
equal (_ ∙ _) (_ ∪ _) = no (λ ())
equal (_ ∙ _) (star _) = no (λ ())
equal (star _) ∅ = no (λ ())
equal (star _) ε = no (λ ())
equal (star _) (lit _) = no (λ ())
equal (star _) (_ ∪ _) = no (λ ())
equal (star _) (_ ∙ _) = no (λ ())

code : (A → ℕ) → Regex A → List ℕ → List ℕ
code rank ∅ rest = 0 ∷ rest
code rank ε rest = 1 ∷ rest
code rank (lit a) rest = 2 ∷ rank a ∷ rest
code rank (r ∪ s) rest = 3 ∷ code rank r (code rank s rest)
code rank (r ∙ s) rest = 4 ∷ code rank r (code rank s rest)
code rank (star r) rest = 5 ∷ code rank r rest

key : (A → ℕ) → Regex A → List ℕ
key rank r = code rank r []
