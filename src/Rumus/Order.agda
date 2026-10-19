{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Rumus.Order {A : Set} (_≟_ : DecidableEquality A) (rank : A → ℕ)
  (rank-injective : ∀ {a b} → rank a ≡ rank b → a ≡ b) where

open import Data.Empty using (⊥)
open import Data.List.Base using (List; []; _∷_)
open import Data.List.Properties using (∷-injective; ∷-injectiveʳ)
open import Data.List.Relation.Binary.Pointwise using (Pointwise; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality.Core using (refl; cong₂)
open import Relation.Binary.Definitions using (Trichotomous; tri<; tri≈; tri>)
open import Relation.Binary.Bundles using (StrictTotalOrder)
import Data.List.Relation.Binary.Lex.Strict as Lex
import Data.Nat.Properties as Nat
open import Rumus.Regex
open import Rumus.Syntax _≟_ using (code; key)

code-tail : ∀ r s xs ys → code rank r xs ≡ code rank s ys → (r ≡ s) × (xs ≡ ys)
code-tail ∅ ∅ xs ys eq = refl , ∷-injectiveʳ eq
code-tail ∅ ε xs ys ()
code-tail ∅ (lit b) xs ys ()
code-tail ∅ (t ∪ u) xs ys ()
code-tail ∅ (t ∙ u) xs ys ()
code-tail ∅ (star t) xs ys ()
code-tail ε ∅ xs ys ()
code-tail ε ε xs ys eq = refl , ∷-injectiveʳ eq
code-tail ε (lit b) xs ys ()
code-tail ε (t ∪ u) xs ys ()
code-tail ε (t ∙ u) xs ys ()
code-tail ε (star t) xs ys ()
code-tail (lit a) ∅ xs ys ()
code-tail (lit a) ε xs ys ()
code-tail (lit a) (lit b) xs ys eq with ∷-injective (∷-injectiveʳ eq)
... | ranks , rest = Relation.Binary.PropositionalEquality.Core.cong lit (rank-injective ranks) , rest
code-tail (lit a) (t ∪ u) xs ys ()
code-tail (lit a) (t ∙ u) xs ys ()
code-tail (lit a) (star t) xs ys ()
code-tail (r ∪ s) ∅ xs ys ()
code-tail (r ∪ s) ε xs ys ()
code-tail (r ∪ s) (lit b) xs ys ()
code-tail (r ∪ s) (t ∪ u) xs ys eq with code-tail r t (code rank s xs) (code rank u ys) (∷-injectiveʳ eq)
... | refl , rest with code-tail s u xs ys rest
...   | refl , refl = refl , refl
code-tail (r ∪ s) (t ∙ u) xs ys ()
code-tail (r ∪ s) (star t) xs ys ()
code-tail (r ∙ s) ∅ xs ys ()
code-tail (r ∙ s) ε xs ys ()
code-tail (r ∙ s) (lit b) xs ys ()
code-tail (r ∙ s) (t ∪ u) xs ys ()
code-tail (r ∙ s) (t ∙ u) xs ys eq with code-tail r t (code rank s xs) (code rank u ys) (∷-injectiveʳ eq)
... | refl , rest with code-tail s u xs ys rest
...   | refl , refl = refl , refl
code-tail (r ∙ s) (star t) xs ys ()
code-tail (star r) ∅ xs ys ()
code-tail (star r) ε xs ys ()
code-tail (star r) (lit b) xs ys ()
code-tail (star r) (t ∪ u) xs ys ()
code-tail (star r) (t ∙ u) xs ys ()
code-tail (star r) (star t) xs ys eq with code-tail r t xs ys (∷-injectiveʳ eq)
... | refl , rest = refl , rest

key-injective : ∀ {r s} → key rank r ≡ key rank s → r ≡ s
key-injective {r} {s} eq = proj₁ (code-tail r s [] [] eq)

pointwise : ∀ {xs ys : List ℕ} → xs ≡ ys → Pointwise _≡_ xs ys
pointwise {[]} refl = []
pointwise {_ ∷ xs} refl = refl ∷ pointwise {xs} refl

unpointwise : ∀ {xs ys : List ℕ} → Pointwise _≡_ xs ys → xs ≡ ys
unpointwise [] = refl
unpointwise (refl ∷ eq) = Relation.Binary.PropositionalEquality.Core.cong (_ ∷_) (unpointwise eq)

module L = StrictTotalOrder (Lex.<-strictTotalOrder Nat.<-strictTotalOrder)

infix 4 _≺_
_≺_ : Regex A → Regex A → Set
r ≺ s = L._<_ (key rank r) (key rank s)

compare : Trichotomous _≡_ _≺_
compare r s with L.compare (key rank r) (key rank s)
... | tri< less neq greater = tri< less (λ { refl → neq (pointwise refl) }) greater
... | tri≈ less eq greater = tri≈ less (key-injective (unpointwise eq)) greater
... | tri> less neq greater = tri> less (λ { refl → neq (pointwise refl) }) greater

≺-trans : ∀ {r s t} → r ≺ s → s ≺ t → r ≺ t
≺-trans = L.trans

≺-irrefl : ∀ {r s} → r ≡ s → r ≺ s → ⊥
≺-irrefl refl less = L.irrefl (pointwise refl) less
