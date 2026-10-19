{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Derivative {A : Set} (_≟_ : DecidableEquality A) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Nullable

derive : A → Regex A → Regex A
derive a ∅ = ∅
derive a ε = ∅
derive a (lit b) with a ≟ b
... | yes _ = ε
... | no _ = ∅
derive a (r ∪ s) = derive a r ∪ derive a s
derive a (r ∙ s) with nullable r
... | yes _ = (derive a r ∙ s) ∪ derive a s
... | no _ = derive a r ∙ s
derive a (star r) = derive a r ∙ star r

derive-sound : ∀ r a {x} → x ∈ derive a r → (a ∷ x) ∈ r
derive-sound ∅ a ()
derive-sound ε a ()
derive-sound (lit b) a p with a ≟ b
... | yes refl with p
...   | empty = literal
derive-sound (lit b) a () | no _
derive-sound (r ∪ s) a (left p) = left (derive-sound r a p)
derive-sound (r ∪ s) a (right p) = right (derive-sound s a p)
derive-sound (r ∙ s) a p with nullable r
... | yes n with p
...   | left (concat h k) = concat (derive-sound r a h) k
...   | right k = concat n (derive-sound s a k)
derive-sound (r ∙ s) a (concat h k) | no _ = concat (derive-sound r a h) k
derive-sound (star r) a (concat h k) = repeat (derive-sound r a h) k

star-peel : ∀ r a →
  (∀ {x} → (a ∷ x) ∈ r → x ∈ derive a r) →
  ∀ {x} → x ∈ star r → ∀ {y} → x ≡ a ∷ y → y ∈ (derive a r ∙ star r)
star-peel r a f stop ()
star-peel r a f (repeat {x = []} p q) eq = star-peel r a f q eq
star-peel r a f (repeat {x = _ ∷ _} p q) refl = concat (f p) q

derive-complete : ∀ r a {x} → (a ∷ x) ∈ r → x ∈ derive a r
derive-complete ∅ a ()
derive-complete ε a ()
derive-complete (lit b) a literal with a ≟ b
... | yes _ = empty
... | no n = ⊥-elim (n refl)
derive-complete (r ∪ s) a (left p) = left (derive-complete r a p)
derive-complete (r ∪ s) a (right p) = right (derive-complete s a p)
derive-complete (r ∙ s) a p with nullable r | concat-view p
... | yes n | [] , _ , refl , h , k = right (derive-complete s a k)
... | yes n | (_ ∷ _) , _ , refl , h , k = left (concat (derive-complete r a h) k)
... | no n | [] , _ , refl , h , k = ⊥-elim (n h)
... | no n | (_ ∷ _) , _ , refl , h , k = concat (derive-complete r a h) k
derive-complete (star r) a p = star-peel r a (derive-complete r a) p refl

derivative-correct : ∀ r a {x} →
  (x ∈ derive a r → (a ∷ x) ∈ r) × ((a ∷ x) ∈ r → x ∈ derive a r)
derivative-correct r a = derive-sound r a , derive-complete r a

derive-cong : ∀ {r s} → r ≈ s → ∀ a → derive a r ≈ derive a s
derive-cong {r} {s} e a =
  (λ p → derive-complete s a (proj₁ e (derive-sound r a p))) ,
  (λ p → derive-complete r a (proj₂ e (derive-sound s a p)))
