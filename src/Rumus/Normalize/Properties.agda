{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Data.Nat.Base using (ℕ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)

module Rumus.Normalize.Properties {A : Set} (_≟_ : DecidableEquality A) (rank : A → ℕ)
  (rank-injective : ∀ {a b} → rank a ≡ rank b → a ≡ b) where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality.Core using (refl; sym; trans; cong; cong₂; subst)
open import Relation.Nullary using (yes; no)
open import Rumus.Regex
open import Rumus.Syntax _≟_ using (equal)
open import Rumus.Normalize _≟_ rank rank-injective

Canonical : List (Regex A) → Set
Canonical = AllPairs _≺_

below-trans : ∀ {r s xs} → r ≺ s → All (s ≺_) xs → All (r ≺_) xs
below-trans less [] = []
below-trans less (h ∷ hs) = ≺-trans less h ∷ below-trans less hs

insert-below : ∀ {s} r xs → s ≺ r → All (s ≺_) xs → All (s ≺_) (insert r xs)
insert-below r [] less [] = less ∷ []
insert-below r (t ∷ ts) less (h ∷ hs) with compare r t
... | tri< _ _ _ = less ∷ h ∷ hs
... | tri≈ _ _ _ = h ∷ hs
... | tri> _ _ _ = h ∷ insert-below r ts less hs

insert-canonical : ∀ r xs → Canonical xs → Canonical (insert r xs)
insert-canonical r [] [] = [] ∷ []
insert-canonical r (s ∷ ss) (bounds ∷ ordered) with compare r s
... | tri< less _ _ = (less ∷ below-trans less bounds) ∷ bounds ∷ ordered
... | tri≈ _ _ _ = bounds ∷ ordered
... | tri> _ _ less = insert-below r ss less bounds ∷ insert-canonical r ss ordered

sort-canonical : ∀ xs → Canonical (sort xs)
sort-canonical [] = []
sort-canonical (r ∷ rs) = insert-canonical r (sort rs) (sort-canonical rs)

insert-first : ∀ r xs → All (r ≺_) xs → insert r xs ≡ r ∷ xs
insert-first r [] [] = refl
insert-first r (s ∷ ss) (less ∷ bounds) with compare r s
... | tri< _ _ _ = refl
... | tri≈ absent _ _ = ⊥-elim (absent less)
... | tri> absent _ _ = ⊥-elim (absent less)

sort-fixed : ∀ {xs} → Canonical xs → sort xs ≡ xs
sort-fixed [] = refl
sort-fixed {r ∷ rs} (bounds ∷ ordered) rewrite sort-fixed ordered = insert-first r rs bounds

all-append : ∀ {P : Regex A → Set} {xs ys} → All P xs → All P ys → All P (Data.List.Base._++_ xs ys)
all-append [] q = q
all-append (p ∷ ps) q = p ∷ all-append ps q

insert-all : ∀ {P : Regex A → Set} r xs → P r → All P xs → All P (insert r xs)
insert-all r [] p [] = p ∷ []
insert-all r (s ∷ ss) p (q ∷ qs) with compare r s
... | tri< _ _ _ = p ∷ q ∷ qs
... | tri≈ _ _ _ = q ∷ qs
... | tri> _ _ _ = q ∷ insert-all r ss p qs

sort-all : ∀ {P : Regex A → Set} {xs} → All P xs → All P (sort xs)
sort-all [] = []
sort-all {xs = r ∷ rs} (p ∷ ps) = insert-all r (sort rs) p (sort-all ps)

Atomic : Regex A → Set
Atomic r = (normalize r ≡ r) × (terms r ≡ (r ∷ []))

pack-terms : ∀ {rs} → All Atomic rs → terms (pack rs) ≡ rs
pack-terms [] = refl
pack-terms ((fixed , flat) ∷ []) = flat
pack-terms {r ∷ s ∷ rs} ((fixed , flat) ∷ atoms) = cong₂ _++_ flat (pack-terms atoms)

pack-fixed : ∀ {rs} → All Atomic rs → Canonical rs → normalize (pack rs) ≡ pack rs
pack-fixed [] [] = refl
pack-fixed ((fixed , flat) ∷ []) ordered = fixed
pack-fixed {r ∷ s ∷ rs} ((fixed , flat) ∷ atoms) (bounds ∷ ordered) =
  trans (cong₂ union fixed (pack-fixed atoms ordered))
    (cong pack (trans (cong sort (cong₂ _++_ flat (pack-terms atoms))) (sort-fixed (bounds ∷ ordered))))

Invariant : Regex A → Set
Invariant r = (normalize r ≡ r) × All Atomic (terms r) × Canonical (terms r)

atomic-invariant : ∀ r → normalize r ≡ r → terms r ≡ (r ∷ []) → Invariant r
atomic-invariant r fixed flat = fixed ,
  subst (All Atomic) (sym flat) ((fixed , flat) ∷ []) ,
  subst Canonical (sym flat) ([] ∷ [])

empty-invariant : Invariant ∅
empty-invariant = refl , [] , []

union-invariant : ∀ r s → Invariant r → Invariant s → Invariant (union r s)
union-invariant r s (fixed-r , atoms-r , ordered-r) (fixed-s , atoms-s , ordered-s) =
  pack-fixed atoms ordered ,
  subst (All Atomic) (sym (pack-terms atoms)) atoms ,
  subst Canonical (sym (pack-terms atoms)) ordered
  where
  atoms : All Atomic (sort (terms (r ∪ s)))
  atoms = sort-all (all-append atoms-r atoms-s)
  ordered : Canonical (sort (terms (r ∪ s)))
  ordered = sort-canonical (terms (r ∪ s))

product-invariant : ∀ r s → Invariant r → Invariant s → Invariant (product r s)
product-invariant r s ir@(fr , ar , cr) is@(fs , as , cs)
  with equal r ∅ in er | equal s ∅ in es | equal r ε in ur | equal s ε in us
... | yes _ | _ | _ | _ = empty-invariant
... | no _ | yes _ | _ | _ = empty-invariant
... | no _ | no _ | yes _ | _ = is
... | no _ | no _ | no _ | yes _ = ir
... | no _ | no _ | no _ | no _ = atomic-invariant (r ∙ s) (trans (cong₂ product fr fs) shape) refl
  where
  shape : product r s ≡ (r ∙ s)
  shape rewrite er | es | ur | us = refl

closure-invariant : ∀ r → Invariant r → Invariant (closure r)
closure-invariant ∅ ir = atomic-invariant ε refl refl
closure-invariant ε ir = atomic-invariant ε refl refl
closure-invariant (star r) ir = ir
closure-invariant (lit a) (fixed , atoms , ordered) = atomic-invariant (star (lit a)) (cong closure fixed) refl
closure-invariant (r ∪ s) (fixed , atoms , ordered) = atomic-invariant (star (r ∪ s)) (cong closure fixed) refl
closure-invariant (r ∙ s) (fixed , atoms , ordered) = atomic-invariant (star (r ∙ s)) (cong closure fixed) refl

normalization-invariant : ∀ r → Invariant (normalize r)
normalization-invariant ∅ = empty-invariant
normalization-invariant ε = atomic-invariant ε refl refl
normalization-invariant (lit a) = atomic-invariant (lit a) refl refl
normalization-invariant (r ∪ s) = union-invariant (normalize r) (normalize s)
  (normalization-invariant r) (normalization-invariant s)
normalization-invariant (r ∙ s) = product-invariant (normalize r) (normalize s)
  (normalization-invariant r) (normalization-invariant s)
normalization-invariant (star r) = closure-invariant (normalize r) (normalization-invariant r)

normalize-idempotent : ∀ r → normalize (normalize r) ≡ normalize r
normalize-idempotent r = proj₁ (normalization-invariant r)

normalize-ordered : ∀ r → Canonical (terms (normalize r))
normalize-ordered r = proj₂ (proj₂ (normalization-invariant r))

open import Rumus.Finite using (_∈ˡ_; append-left; append-right)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

insert-cover : ∀ r rs {q} → q ∈ˡ (r ∷ rs) → q ∈ˡ insert r rs
insert-cover r [] h = h
insert-cover r (s ∷ ss) h with compare r s
... | tri< _ _ _ = h
... | tri≈ _ refl _ with h
...   | here eq = here eq
...   | there p = p
insert-cover r (s ∷ ss) h | tri> _ _ _ with h
... | here eq = there (insert-cover r ss (here eq))
... | there (here eq) = here eq
... | there (there p) = there (insert-cover r ss (there p))

insert-extract : ∀ r rs {q} → q ∈ˡ insert r rs → q ∈ˡ (r ∷ rs)
insert-extract r [] h = h
insert-extract r (s ∷ ss) h with compare r s
... | tri< _ _ _ = h
... | tri≈ _ _ _ = there h
... | tri> _ _ _ with h
...   | here eq = there (here eq)
...   | there p with insert-extract r ss p
...     | here eq = here eq
...     | there p = there (there p)

sort-cover : ∀ {rs q} → q ∈ˡ rs → q ∈ˡ sort rs
sort-cover {r ∷ rs} (here eq) = insert-cover r (sort rs) (here eq)
sort-cover {r ∷ rs} (there h) = insert-cover r (sort rs) (there (sort-cover h))

sort-extract : ∀ {rs q} → q ∈ˡ sort rs → q ∈ˡ rs
sort-extract {r ∷ rs} h with insert-extract r (sort rs) h
... | here eq = here eq
... | there h = there (sort-extract h)

all-lookup : ∀ {P : Regex A → Set} {q rs} → q ∈ˡ rs → All P rs → P q
all-lookup (here refl) (p ∷ ps) = p
all-lookup (there h) (p ∷ ps) = all-lookup h ps

canonical-unique : ∀ {xs ys} → Canonical xs → Canonical ys →
  (∀ q → q ∈ˡ xs → q ∈ˡ ys) → (∀ q → q ∈ˡ ys → q ∈ˡ xs) → xs ≡ ys
canonical-unique [] [] to from = refl
canonical-unique {xs = []} {ys = y ∷ ys} [] ordered to from with from y (here refl)
... | ()
canonical-unique {xs = x ∷ xs} ordered [] to from with to x (here refl)
... | ()
canonical-unique {xs = x ∷ xs} {y ∷ ys} (bx ∷ cx) (by ∷ cy) to from with compare x y
... | tri< less _ _ with to x (here refl)
...   | here eq = ⊥-elim (≺-irrefl eq less)
...   | there h = ⊥-elim (≺-irrefl refl (≺-trans less (all-lookup h by)))
canonical-unique {xs = x ∷ xs} {y ∷ ys} (bx ∷ cx) (by ∷ cy) to from | tri> _ _ less with from y (here refl)
... | here eq = ⊥-elim (≺-irrefl eq less)
... | there h = ⊥-elim (≺-irrefl refl (≺-trans less (all-lookup h bx)))
canonical-unique {xs = x ∷ xs} {.x ∷ ys} (bx ∷ cx) (by ∷ cy) to from | tri≈ _ refl _ =
  cong (x ∷_) (canonical-unique cx cy forward backward)
  where
  forward : ∀ q → q ∈ˡ xs → q ∈ˡ ys
  forward q h with to q (there h)
  ... | here eq = ⊥-elim (≺-irrefl (sym eq) (all-lookup h bx))
  ... | there k = k
  backward : ∀ q → q ∈ˡ ys → q ∈ˡ xs
  backward q h with from q (there h)
  ... | here eq = ⊥-elim (≺-irrefl (sym eq) (all-lookup h by))
  ... | there k = k

sort-cong : ∀ {xs ys} → (∀ q → q ∈ˡ xs → q ∈ˡ ys) → (∀ q → q ∈ˡ ys → q ∈ˡ xs) → sort xs ≡ sort ys
sort-cong {xs} {ys} to from = canonical-unique (sort-canonical xs) (sort-canonical ys)
  (λ q h → sort-cover (to q (sort-extract h))) (λ q h → sort-cover (from q (sort-extract h)))

append-view : ∀ {q : Regex A} xs {ys} → q ∈ˡ (xs ++ ys) → (q ∈ˡ xs) ⊎ (q ∈ˡ ys)
append-view [] h = inj₂ h
append-view (_ ∷ xs) (here eq) = inj₁ (here eq)
append-view (_ ∷ xs) (there h) with append-view xs h
... | inj₁ p = inj₁ (there p)
... | inj₂ p = inj₂ p

append-swap : ∀ xs ys {q} → q ∈ˡ (xs ++ ys) → q ∈ˡ (ys ++ xs)
append-swap xs ys h with append-view xs h
... | inj₁ p = append-right ys p
... | inj₂ p = append-left xs p

union-commutative : ∀ r s → union r s ≡ union s r
union-commutative r s = cong pack (sort-cong (λ _ → append-swap (terms r) (terms s)) (λ _ → append-swap (terms s) (terms r)))

normalize-union-commutative : ∀ r s → normalize (r ∪ s) ≡ normalize (s ∪ r)
normalize-union-commutative r s = union-commutative (normalize r) (normalize s)

Flat : Regex A → Set
Flat r = terms r ≡ (r ∷ [])

flat-terms : ∀ r → All Flat (terms r)
flat-terms ∅ = []
flat-terms ε = refl ∷ []
flat-terms (lit a) = refl ∷ []
flat-terms (r ∪ s) = all-append (flat-terms r) (flat-terms s)
flat-terms (r ∙ s) = refl ∷ []
flat-terms (star r) = refl ∷ []

pack-flat : ∀ {rs} → All Flat rs → terms (pack rs) ≡ rs
pack-flat [] = refl
pack-flat (h ∷ []) = h
pack-flat {r ∷ s ∷ rs} (h ∷ hs) = cong₂ _++_ h (pack-flat hs)

union-terms : ∀ r s → terms (union r s) ≡ sort (terms r ++ terms s)
union-terms r s = pack-flat (sort-all (all-append (flat-terms r) (flat-terms s)))

union-cover : ∀ r s {q} → q ∈ˡ (terms r ++ terms s) → q ∈ˡ terms (union r s)
union-cover r s h = subst (_ ∈ˡ_) (sym (union-terms r s)) (sort-cover h)

union-extract : ∀ r s {q} → q ∈ˡ terms (union r s) → q ∈ˡ (terms r ++ terms s)
union-extract r s h = sort-extract (subst (_ ∈ˡ_) (union-terms r s) h)

union-associative : ∀ r s t → union (union r s) t ≡ union r (union s t)
union-associative r s t = cong pack (sort-cong forward backward)
  where
  forward : ∀ q → q ∈ˡ (terms (union r s) ++ terms t) → q ∈ˡ (terms r ++ terms (union s t))
  forward q h with append-view (terms (union r s)) h
  ... | inj₂ p = append-right (terms r) (union-cover s t (append-right (terms s) p))
  ... | inj₁ p with append-view (terms r) (union-extract r s p)
  ...   | inj₁ k = append-left (terms (union s t)) k
  ...   | inj₂ k = append-right (terms r) (union-cover s t (append-left (terms t) k))
  backward : ∀ q → q ∈ˡ (terms r ++ terms (union s t)) → q ∈ˡ (terms (union r s) ++ terms t)
  backward q h with append-view (terms r) h
  ... | inj₁ p = append-left (terms t) (union-cover r s (append-left (terms s) p))
  ... | inj₂ p with append-view (terms s) (union-extract s t p)
  ...   | inj₁ k = append-left (terms t) (union-cover r s (append-right (terms r) k))
  ...   | inj₂ k = append-right (terms (union r s)) k

normalize-union-associative : ∀ r s t → normalize ((r ∪ s) ∪ t) ≡ normalize (r ∪ (s ∪ t))
normalize-union-associative r s t = union-associative (normalize r) (normalize s) (normalize t)
