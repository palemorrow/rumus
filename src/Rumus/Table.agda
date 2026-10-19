{-# OPTIONS --safe --without-K #-}

module Rumus.Table where

open import Data.List.Base using (List; []; _∷_; map)
open import Data.Product.Base using (_×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (yes; no)

Table : Set → Set → Set
Table X Y = List (X × Y)

tabulate : ∀ {X Y : Set} → List X → (X → Y) → Table X Y
tabulate xs f = map (λ x → x , f x) xs

lookup : ∀ {X Y : Set} → DecidableEquality X → Table X Y → (X → Y) → X → Y
lookup eq [] fallback x = fallback x
lookup eq ((y , value) ∷ entries) fallback x with eq x y
... | yes _ = value
... | no _ = lookup eq entries fallback x

lookup-correct : ∀ {X Y : Set} (eq : DecidableEquality X) xs (f : X → Y) x →
  lookup eq (tabulate xs f) f x ≡ f x
lookup-correct eq [] f x = refl
lookup-correct eq (y ∷ ys) f x with eq x y
... | yes refl = refl
... | no _ = lookup-correct eq ys f x
