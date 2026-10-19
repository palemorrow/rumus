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

key : (A → ℕ) → Regex A → List ℕ
key rank ∅ = 0 ∷ []
key rank ε = 1 ∷ []
key rank (lit a) = 2 ∷ rank a ∷ []
key rank (r ∪ s) = 3 ∷ (key rank r ++ key rank s)
key rank (r ∙ s) = 4 ∷ (key rank r ++ key rank s)
key rank (star r) = 5 ∷ key rank r
