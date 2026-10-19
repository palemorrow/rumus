{-# OPTIONS --safe --without-K #-}

module Rumus.Nullable where

open import Data.List.Base using ([]; _∷_)
open import Data.Product.Base using (proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Rumus.Regex
open import Rumus.Language

nullable : ∀ {A} (r : Regex A) → Dec ([] ∈ r)
nullable ∅ = no (λ ())
nullable ε = yes empty
nullable (lit a) = no (λ ())
nullable (r ∪ s) with nullable r | nullable s
... | yes p | _ = yes (left p)
... | no _ | yes q = yes (right q)
... | no p | no q = no λ { (left h) → p h ; (right h) → q h }
nullable (r ∙ s) with nullable r | nullable s
... | yes p | yes q = yes (concat p q)
... | no p | _ = no λ h → p (proj₁ (concat-empty h))
... | _ | no q = no λ h → q (proj₂ (concat-empty h))
nullable (star r) = yes stop
