{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Rumus.Normalize {A : Set} (_≟_ : DecidableEquality A) (rank : A → ℕ)
  (rank-injective : ∀ {a b} → rank a ≡ rank b → a ≡ b) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Nat.Base using (ℕ; _<ᵇ_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (yes; no)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Algebra
open import Rumus.Syntax _≟_

private
  lex-less : List ℕ → List ℕ → Bool
  lex-less [] [] = false
  lex-less [] (_ ∷ _) = true
  lex-less (_ ∷ _) [] = false
  lex-less (x ∷ xs) (y ∷ ys) with x <ᵇ y | y <ᵇ x
  ... | true | _ = true
  ... | false | true = false
  ... | false | false = lex-less xs ys

sum : List (Regex A) → Regex A
sum [] = ∅
sum (r ∷ rs) = r ∪ sum rs

insert : Regex A → List (Regex A) → List (Regex A)
insert r [] = r ∷ []
insert r (s ∷ ss) with equal r s | lex-less (key rank r) (key rank s)
... | yes _ | _ = s ∷ ss
... | no _ | true = r ∷ s ∷ ss
... | no _ | false = s ∷ insert r ss

insert-correct : ∀ r rs → sum (insert r rs) ≈ (r ∪ sum rs)
insert-correct r [] = ≈-refl
insert-correct r (s ∷ ss) with equal r s | lex-less (key rank r) (key rank s)
... | yes refl | _ = ≈-sym (≈-trans (≈-sym union-assoc) (union-cong union-idem ≈-refl))
... | no _ | true = ≈-refl
... | no _ | false = ≈-trans (union-cong ≈-refl (insert-correct r ss))
  (≈-trans (≈-sym union-assoc) (≈-trans (union-cong union-comm ≈-refl) union-assoc))

sort : List (Regex A) → List (Regex A)
sort [] = []
sort (r ∷ rs) = insert r (sort rs)

sort-correct : ∀ rs → sum (sort rs) ≈ sum rs
sort-correct [] = ≈-refl
sort-correct (r ∷ rs) = ≈-trans (insert-correct r (sort rs)) (union-cong ≈-refl (sort-correct rs))

terms : Regex A → List (Regex A)
terms ∅ = []
terms (r ∪ s) = terms r ++ terms s
terms ε = ε ∷ []
terms (lit a) = lit a ∷ []
terms (r ∙ s) = (r ∙ s) ∷ []
terms (star r) = star r ∷ []

sum-append : ∀ rs ss → sum (rs ++ ss) ≈ (sum rs ∪ sum ss)
sum-append [] ss = ≈-sym union-emptyˡ
sum-append (r ∷ rs) ss = ≈-trans (union-cong ≈-refl (sum-append rs ss)) (≈-sym union-assoc)

terms-correct : ∀ r → sum (terms r) ≈ r
terms-correct ∅ = ≈-refl
terms-correct (r ∪ s) = ≈-trans (sum-append (terms r) (terms s)) (union-cong (terms-correct r) (terms-correct s))
terms-correct ε = union-emptyʳ
terms-correct (lit a) = union-emptyʳ
terms-correct (r ∙ s) = union-emptyʳ
terms-correct (star r) = union-emptyʳ

drop-zero : Regex A → Regex A → Regex A
drop-zero r s with equal r ∅ | equal s ∅
... | yes _ | _ = s
... | no _ | yes _ = r
... | no _ | no _ = r ∪ s

drop-zero-correct : ∀ r s → drop-zero r s ≈ (r ∪ s)
drop-zero-correct r s with equal r ∅ | equal s ∅
... | yes refl | _ = ≈-sym union-emptyˡ
... | no _ | yes refl = ≈-sym union-emptyʳ
... | no _ | no _ = ≈-refl

trim : Regex A → Regex A
trim (r ∪ s) = drop-zero (trim r) (trim s)
trim r = r

trim-correct : ∀ r → trim r ≈ r
trim-correct (r ∪ s) = ≈-trans (drop-zero-correct (trim r) (trim s))
  (union-cong (trim-correct r) (trim-correct s))
trim-correct ∅ = ≈-refl
trim-correct ε = ≈-refl
trim-correct (lit _) = ≈-refl
trim-correct (_ ∙ _) = ≈-refl
trim-correct (star _) = ≈-refl

union : Regex A → Regex A → Regex A
union r s = trim (sum (sort (terms (r ∪ s))))

union-correct : ∀ r s → union r s ≈ (r ∪ s)
union-correct r s = ≈-trans (trim-correct (sum (sort (terms (r ∪ s)))))
  (≈-trans (sort-correct (terms (r ∪ s))) (terms-correct (r ∪ s)))

product : Regex A → Regex A → Regex A
product r s with equal r ∅ | equal s ∅ | equal r ε | equal s ε
... | yes _ | _ | _ | _ = ∅
... | no _ | yes _ | _ | _ = ∅
... | no _ | no _ | yes _ | _ = s
... | no _ | no _ | no _ | yes _ = r
... | no _ | no _ | no _ | no _ = r ∙ s

product-correct : ∀ r s → product r s ≈ (r ∙ s)
product-correct r s with equal r ∅ | equal s ∅ | equal r ε | equal s ε
... | yes refl | _ | _ | _ = ≈-sym concat-zeroˡ
... | no _ | yes refl | _ | _ = ≈-sym concat-zeroʳ
... | no _ | no _ | yes refl | _ = ≈-sym concat-unitˡ
... | no _ | no _ | no _ | yes refl = ≈-sym concat-unitʳ
... | no _ | no _ | no _ | no _ = ≈-refl

closure : Regex A → Regex A
closure ∅ = ε
closure ε = ε
closure (star r) = star r
closure r = star r

closure-correct : ∀ r → closure r ≈ star r
closure-correct ∅ = ≈-sym star-empty
closure-correct ε = ≈-sym star-epsilon
closure-correct (star r) = ≈-sym star-idem
closure-correct (lit a) = ≈-refl
closure-correct (r ∪ s) = ≈-refl
closure-correct (r ∙ s) = ≈-refl

normalize : Regex A → Regex A
normalize ∅ = ∅
normalize ε = ε
normalize (lit a) = lit a
normalize (r ∪ s) = union (normalize r) (normalize s)
normalize (r ∙ s) = product (normalize r) (normalize s)
normalize (star r) = closure (normalize r)

normalize-correct : ∀ r → normalize r ≈ r
normalize-correct ∅ = ≈-refl
normalize-correct ε = ≈-refl
normalize-correct (lit a) = ≈-refl
normalize-correct (r ∪ s) = ≈-trans (union-correct (normalize r) (normalize s))
  (union-cong (normalize-correct r) (normalize-correct s))
normalize-correct (r ∙ s) = ≈-trans (product-correct (normalize r) (normalize s))
  (concat-cong (normalize-correct r) (normalize-correct s))
normalize-correct (star r) = ≈-trans (closure-correct (normalize r)) (star-cong (normalize-correct r))
