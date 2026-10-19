{-# OPTIONS --safe --without-K #-}

module Rumus.Finite where

open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (ℕ; _≤_; _<_; z≤n; s≤s)
open import Data.List.Base using (length; concatMap)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; subst; sym)
open import Relation.Nullary using (Dec; yes; no)
open import Rumus.Regex
open import Rumus.Language using (_≈_; _∈_)
open import Rumus.Join

infix 4 _∈ˡ_

_∈ˡ_ : ∀ {X : Set} → X → List X → Set
x ∈ˡ xs = Any (x ≡_) xs

member : ∀ {X : Set} → DecidableEquality X → (x : X) (xs : List X) → Dec (x ∈ˡ xs)
member eq x [] = no (λ ())
member eq x (y ∷ ys) with eq x y | member eq x ys
... | yes p | _ = yes (here p)
... | no _ | yes p = yes (there p)
... | no n | no m = no λ { (here p) → n p ; (there p) → m p }

any-inject : ∀ {X : Set} {P : X → Set} {x xs} → x ∈ˡ xs → P x → Any P xs
any-inject (here refl) p = here p
any-inject (there m) p = there (any-inject m p)

any-extract : ∀ {X : Set} {P : X → Set} {xs} → Any P xs → Σ X λ x → (x ∈ˡ xs) × P x
any-extract (here p) = _ , here refl , p
any-extract (there m) with any-extract m
... | x , k , p = x , there k , p

map-member : ∀ {X Y : Set} (f : X → Y) {x xs} → x ∈ˡ xs → f x ∈ˡ map f xs
map-member f (here refl) = here refl
map-member f (there p) = there (map-member f p)

append-left : ∀ {X : Set} {x : X} {xs} ys → x ∈ˡ xs → x ∈ˡ (xs ++ ys)
append-left ys (here p) = here p
append-left ys (there p) = there (append-left ys p)

append-right : ∀ {X : Set} {x : X} xs {ys} → x ∈ˡ ys → x ∈ˡ (xs ++ ys)
append-right [] p = p
append-right (_ ∷ xs) p = there (append-right xs p)

data Selection {X : Set} : List X → Set where
  done : Selection []
  take skip : ∀ {x xs} → Selection xs → Selection (x ∷ xs)

selected : ∀ {X : Set} {xs : List X} → Selection xs → List X
selected done = []
selected (take {x} ps) = x ∷ selected ps
selected (skip ps) = selected ps

selections : ∀ {X : Set} (xs : List X) → List (Selection xs)
selections [] = done ∷ []
selections (_ ∷ xs) = map skip (selections xs) ++ map take (selections xs)

selections-complete : ∀ {X : Set} {xs : List X} (s : Selection xs) → s ∈ˡ selections xs
selections-complete done = here refl
selections-complete (take {xs = xs} s) = append-right (map skip (selections xs)) (map-member take (selections-complete s))
selections-complete (skip {xs = xs} s) = append-left (map take (selections xs)) (map-member skip (selections-complete s))

selection-equal : ∀ {X : Set} {xs : List X} → DecidableEquality (Selection xs)
selection-equal done done = yes refl
selection-equal (take p) (skip q) = no (λ ())
selection-equal (skip p) (take q) = no (λ ())
selection-equal (take p) (take q) with selection-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
selection-equal (skip p) (skip q) with selection-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }

select : ∀ {X : Set} → DecidableEquality X → (xs : List X) → List X → Selection xs
select eq [] ps = done
select eq (x ∷ xs) ps with member eq x ps
... | yes _ = take (select eq xs ps)
... | no _ = skip (select eq xs ps)

select-sound : ∀ {X : Set} (eq : DecidableEquality X) xs ps {x} →
  x ∈ˡ selected (select eq xs ps) → x ∈ˡ ps
select-sound eq [] ps ()
select-sound eq (y ∷ ys) ps p with member eq y ps
... | yes m with p
...   | here refl = m
...   | there k = select-sound eq ys ps k
select-sound eq (y ∷ ys) ps p | no _ = select-sound eq ys ps p

select-complete : ∀ {X : Set} (eq : DecidableEquality X) xs ps {x} →
  x ∈ˡ xs → x ∈ˡ ps → x ∈ˡ selected (select eq xs ps)
select-complete eq (y ∷ ys) ps e p with member eq y ps
... | yes m with e
...   | here refl = here refl
...   | there k = there (select-complete eq ys ps k p)
select-complete eq (y ∷ ys) ps (here refl) p | no n = ⊥-elim (n p)
select-complete eq (y ∷ ys) ps (there k) p | no n = select-complete eq ys ps k p

selection-correct : ∀ {A X : Set} (eq : DecidableEquality X)
  (f : X → Regex A) (xs : List X) → (∀ x → x ∈ˡ xs) → ∀ ps →
  join f (selected (select eq xs ps)) ≈ join f ps
selection-correct eq f xs all ps =
  (λ p → forward (any-extract (join-sound p))) ,
  (λ p → backward (any-extract (join-sound p)))
  where
  forward : ∀ {w} → (Σ _ λ x → (x ∈ˡ selected (select eq xs ps)) × (w ∈ f x)) → w ∈ join f ps
  forward (x , m , p) = join-complete (any-inject (select-sound eq xs ps m) p)
  backward : ∀ {w} → (Σ _ λ x → (x ∈ˡ ps) × (w ∈ f x)) → w ∈ join f (selected (select eq xs ps))
  backward (x , m , p) = join-complete (any-inject (select-complete eq xs ps (all x) m) p)

cartesian : ∀ {X Y : Set} → List X → List Y → List (X × Y)
cartesian xs ys = concatMap (λ x → map (x ,_) ys) xs

cartesian-member : ∀ {X Y : Set} {x : X} {y : Y} {xs ys} →
  x ∈ˡ xs → y ∈ˡ ys → (x , y) ∈ˡ cartesian xs ys
cartesian-member {xs = _ ∷ xs} {ys} (here refl) q = append-left (cartesian xs ys) (map-member (_ ,_) q)
cartesian-member {xs = x ∷ xs} {ys} (there p) q = append-right (map (x ,_) ys) (cartesian-member p q)

remove : ∀ {X : Set} → DecidableEquality X → X → List X → List X
remove eq x [] = []
remove eq x (y ∷ ys) with eq x y
... | yes _ = remove eq x ys
... | no _ = y ∷ remove eq x ys

≤-next : ∀ {n m} → n ≤ m → n ≤ Data.Nat.Base.suc m
≤-next z≤n = z≤n
≤-next (s≤s p) = s≤s (≤-next p)

remove-length : ∀ {X : Set} (eq : DecidableEquality X) x xs → length (remove eq x xs) ≤ length xs
remove-length eq x [] = z≤n
remove-length eq x (y ∷ ys) with eq x y
... | yes _ = ≤-next (remove-length eq x ys)
... | no _ = s≤s (remove-length eq x ys)

remove-shorter : ∀ {X : Set} (eq : DecidableEquality X) x xs →
  x ∈ˡ xs → length (remove eq x xs) < length xs
remove-shorter eq x [] ()
remove-shorter eq x (y ∷ ys) p with eq x y
... | yes _ = s≤s (remove-length eq x ys)
... | no n with p
...   | here e = ⊥-elim (n e)
...   | there k = s≤s (remove-shorter eq x ys k)

remove-preserve : ∀ {X : Set} (eq : DecidableEquality X) x xs {y} →
  (y ≡ x → Data.Empty.⊥) → y ∈ˡ xs → y ∈ˡ remove eq x xs
remove-preserve eq x [] n ()
remove-preserve eq x (z ∷ zs) n p with eq x z
... | yes refl with p
...   | here e = ⊥-elim (n e)
...   | there k = remove-preserve eq x zs n k
remove-preserve eq x (z ∷ zs) n (here e) | no _ = here e
remove-preserve eq x (z ∷ zs) n (there k) | no _ = there (remove-preserve eq x zs n k)

adjoin : ∀ {X : Set} → DecidableEquality X → X → List X → List X
adjoin eq x xs with member eq x xs
... | yes _ = xs
... | no _ = x ∷ xs

adjoin-head : ∀ {X : Set} (eq : DecidableEquality X) x xs → x ∈ˡ adjoin eq x xs
adjoin-head eq x xs with member eq x xs
... | yes h = h
... | no _ = here refl

adjoin-tail : ∀ {X : Set} (eq : DecidableEquality X) x xs {y} → y ∈ˡ xs → y ∈ˡ adjoin eq x xs
adjoin-tail eq x xs h with member eq x xs
... | yes _ = h
... | no _ = there h

unique : ∀ {X : Set} → DecidableEquality X → List X → List X
unique eq [] = []
unique eq (x ∷ xs) = adjoin eq x (unique eq xs)

unique-cover : ∀ {X : Set} (eq : DecidableEquality X) {x xs} → x ∈ˡ xs → x ∈ˡ unique eq xs
unique-cover eq {xs = y ∷ ys} (here refl) = adjoin-head eq y (unique eq ys)
unique-cover eq {xs = y ∷ ys} (there h) = adjoin-tail eq y (unique eq ys) (unique-cover eq h)

backwards : ∀ {X : Set} → List X → List X
backwards [] = []
backwards (x ∷ xs) = backwards xs ++ (x ∷ [])

backwards-cover : ∀ {X : Set} {x : X} {xs} → x ∈ˡ xs → x ∈ˡ backwards xs
backwards-cover {xs = y ∷ ys} (here refl) = append-right (backwards ys) (here refl)
backwards-cover {xs = y ∷ ys} (there h) = append-left (y ∷ []) (backwards-cover h)
