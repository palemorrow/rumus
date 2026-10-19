{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Data.Nat.Base using (ℕ)

module Rumus.NormalizedMatch {A : Set} (_≟_ : DecidableEquality A) (rank : A → ℕ)
  (rank-injective : ∀ {a b} → rank a ≡ rank b → a ≡ b) where

open import Data.Bool.Base using (Bool; true)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (Dec; yes; no; does)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Nullable
open import Rumus.Derivative _≟_
open import Rumus.Normalize _≟_ rank rank-injective

step : A → Regex A → Regex A
step a r = normalize (derive a r)

match : (r : Regex A) (x : List A) → Dec (x ∈ r)
match r [] = nullable r
match r (a ∷ x) with match (step a r) x
... | yes p = yes (derive-sound r a (proj₁ (normalize-correct (derive a r)) p))
... | no n = no (λ p → n (proj₂ (normalize-correct (derive a r)) (derive-complete r a p)))

accepts : Regex A → List A → Bool
accepts r x = does (match r x)

sound : ∀ r x → accepts r x ≡ true → x ∈ r
sound r x with match r x
... | yes p = λ _ → p
... | no _ = λ ()

complete : ∀ r x → x ∈ r → accepts r x ≡ true
complete r x p with match r x
... | yes _ = refl
... | no n = ⊥-elim (n p)
