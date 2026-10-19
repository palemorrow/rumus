{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Match {A : Set} (_≟_ : DecidableEquality A) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no; does)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Nullable
open import Rumus.Derivative _≟_

match : (r : Regex A) (x : List A) → Dec (x ∈ r)
match r [] = nullable r
match r (a ∷ x) with match (derive a r) x
... | yes p = yes (derive-sound r a p)
... | no n = no (λ p → n (derive-complete r a p))

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

reject : ∀ r x → accepts r x ≡ false → x ∈ r → Data.Empty.⊥
reject r x with match r x
... | yes _ = λ ()
... | no n = λ _ → n
