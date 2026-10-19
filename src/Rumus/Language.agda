{-# OPTIONS --safe --without-K #-}

module Rumus.Language where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_×_; _,_; Σ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst)
open import Rumus.Regex

infix 4 _∈_ _≈_

data _∈_ {A : Set} : List A → Regex A → Set where
  empty : [] ∈ ε
  literal : ∀ {a} → (a ∷ []) ∈ lit a
  left : ∀ {x r s} → x ∈ r → x ∈ (r ∪ s)
  right : ∀ {x r s} → x ∈ s → x ∈ (r ∪ s)
  concat : ∀ {x y r s} → x ∈ r → y ∈ s → (x ++ y) ∈ (r ∙ s)
  stop : ∀ {r} → [] ∈ star r
  repeat : ∀ {x y r} → x ∈ r → y ∈ star r → (x ++ y) ∈ star r

_≈_ : ∀ {A} → Regex A → Regex A → Set
r ≈ s = ∀ {x} → (x ∈ r → x ∈ s) × (x ∈ s → x ∈ r)

≈-refl : ∀ {A} {r : Regex A} → r ≈ r
≈-refl = (λ p → p) , (λ p → p)

≈-sym : ∀ {A} {r s : Regex A} → r ≈ s → s ≈ r
≈-sym e = (λ p → Data.Product.Base.proj₂ e p) , (λ p → Data.Product.Base.proj₁ e p)

≈-trans : ∀ {A} {r s t : Regex A} → r ≈ s → s ≈ t → r ≈ t
≈-trans e f = (λ p → Data.Product.Base.proj₁ f (Data.Product.Base.proj₁ e p)) ,
              (λ p → Data.Product.Base.proj₂ e (Data.Product.Base.proj₂ f p))

transport : ∀ {A} {x y : List A} {r} → x ≡ y → x ∈ r → y ∈ r
transport refl p = p

concat-view : ∀ {A} {z : List A} {r s} → z ∈ (r ∙ s) →
  Σ (List A) λ x → Σ (List A) λ y → (z ≡ x ++ y) × (x ∈ r) × (y ∈ s)
concat-view (concat {x = x} {y} p q) = x , y , refl , p , q

concat-empty : ∀ {A} {r s : Regex A} → [] ∈ (r ∙ s) → ([] ∈ r) × ([] ∈ s)
concat-empty p with concat-view p
... | [] , [] , refl , h , k = h , k
