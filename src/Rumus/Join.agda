{-# OPTIONS --safe --without-K #-}

module Rumus.Join where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Algebra

join : ∀ {A X : Set} → (X → Regex A) → List X → Regex A
join f [] = ∅
join f (p ∷ ps) = f p ∪ join f ps

join-map : ∀ {A X Y : Set} (f : Y → Regex A) (g : X → Y) ps →
  join f (map g ps) ≡ join (λ p → f (g p)) ps
join-map f g [] = refl
join-map f g (p ∷ ps) = cong (f (g p) ∪_) (join-map f g ps)

join-map-correct : ∀ {A X Y : Set} (f : Y → Regex A) (g : X → Y) ps →
  join f (map g ps) ≈ join (λ p → f (g p)) ps
join-map-correct f g ps rewrite join-map f g ps = ≈-refl

join-append : ∀ {A X : Set} (f : X → Regex A) ps qs →
  join f (ps ++ qs) ≈ (join f ps ∪ join f qs)
join-append f [] qs = ≈-sym union-emptyˡ
join-append f (p ∷ ps) qs = ≈-trans (union-cong ≈-refl (join-append f ps qs)) (≈-sym union-assoc)

join-concat : ∀ {A X : Set} (f : X → Regex A) ps s →
  join (λ p → f p ∙ s) ps ≈ (join f ps ∙ s)
join-concat f [] s = ≈-sym concat-zeroˡ
join-concat f (p ∷ ps) s = ≈-trans (union-cong ≈-refl (join-concat f ps s)) (≈-sym distribute)

join-sound : ∀ {A X : Set} {f : X → Regex A} {ps x} →
  x ∈ join f ps → Any (λ p → x ∈ f p) ps
join-sound {ps = _ ∷ _} (left p) = here p
join-sound {ps = _ ∷ _} (right p) = there (join-sound p)

join-complete : ∀ {A X : Set} {f : X → Regex A} {ps x} →
  Any (λ p → x ∈ f p) ps → x ∈ join f ps
join-complete (here p) = left p
join-complete (there p) = right (join-complete p)
