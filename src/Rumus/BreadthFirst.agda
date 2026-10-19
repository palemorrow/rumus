{-# OPTIONS --safe --without-K --erasure --erased-matches #-}

open import Rumus.Machine using (Machine)
open import Data.List.Base using (List)

module Rumus.BreadthFirst {A : Set} (m n : Machine A) (alphabet : List A) where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_; _++_; map; concatMap; length; initLast; _∷ʳ′_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Product.Base using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Data.Nat.Base using (ℕ; zero; suc; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≤-refl; _≤?_; ≰⇒>)
open import Data.Nat.Induction using (Acc; acc; <-wellFounded)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans; cong; subst)
open import Relation.Nullary using (yes; no)
open import Rumus.Finite
open import Rumus.Machine using (State; run; output; Accept)
open import Rumus.Bisimulation m n alphabet public
  using (Pair; pair-equal; universe; universe-complete; successor; Good; Witness; Closed; On; bisimilar)
open import Rumus.Worklist m n alphabet using (Known; Frontier; Cover)

run-pair : Pair → List A → Pair
run-pair (p , q) x = run m p x , run n q x

run-append : ∀ q x y → run-pair q (x ++ y) ≡ run-pair (run-pair q x) y
run-append q [] y = refl
run-append q (a ∷ x) y = run-append (successor q a) x y

Separates : Pair → List A → Set
Separates (p , q) x = ((Accept m p x) × (Accept n q x → ⊥)) ⊎ ((Accept n q x) × (Accept m p x → ⊥))

record Shortest (start : Pair) : Set where
  constructor shortest
  field
    word : List A
    witness : Separates start word
    supported : All (λ a → a ∈ˡ alphabet) word
    minimal : ∀ x → All (λ a → a ∈ˡ alphabet) x → Separates start x → length word ≤ length x

record Path (start : Pair) (depth : ℕ) (q : Pair) : Set where
  constructor path
  field
    word : List A
    endpoint : run-pair start word ≡ q
    distance : length word ≡ depth
    supported : All (λ a → a ∈ˡ alphabet) word

all-lookup : ∀ {X : Set} {P : X → Set} {q xs} → q ∈ˡ xs → All P xs → P q
all-lookup (here refl) (p ∷ ps) = p
all-lookup (there h) (p ∷ ps) = all-lookup h ps

all-append : ∀ {X : Set} {P : X → Set} {xs ys} → All P xs → All P ys → All P (xs ++ ys)
all-append [] q = q
all-append (p ∷ ps) q = p ∷ all-append ps q

append-view : ∀ {X : Set} {q : X} xs {ys} → q ∈ˡ (xs ++ ys) → (q ∈ˡ xs) ⊎ (q ∈ˡ ys)
append-view [] h = inj₂ h
append-view (_ ∷ xs) (here h) = inj₁ (here h)
append-view (_ ∷ xs) (there h) with append-view xs h
... | inj₁ p = inj₁ (there p)
... | inj₂ p = inj₂ p

fresh : List Pair → List Pair → List Pair
fresh seen [] = []
fresh seen (q ∷ qs) with member pair-equal q seen
... | yes _ = fresh seen qs
... | no _ = q ∷ fresh seen qs

fresh-cover : ∀ seen {qs q} → q ∈ˡ qs → Known seen (fresh seen qs) q
fresh-cover seen {p ∷ qs} h with member pair-equal p seen
... | yes present with h
...   | here refl = inj₁ present
...   | there h = fresh-cover seen h
fresh-cover seen {p ∷ qs} h | no absent with h
... | here refl = inj₂ (here refl)
... | there h with fresh-cover seen h
...   | inj₁ p = inj₁ p
...   | inj₂ p = inj₂ (there p)

fresh-member : ∀ seen {qs q} → q ∈ˡ fresh seen qs → (q ∈ˡ qs) × (q ∈ˡ seen → ⊥)
fresh-member seen {p ∷ qs} h with member pair-equal p seen
... | yes _ with fresh-member seen h
...   | k , absent = there k , absent
fresh-member seen {p ∷ qs} h | no absent with h
... | here refl = here refl , absent
... | there h with fresh-member seen h
...   | k , absent = there k , absent

fresh-all : ∀ {P : Pair → Set} seen {qs} → All P qs → All P (fresh seen qs)
fresh-all seen [] = []
fresh-all seen {qs = q ∷ qs} (p ∷ ps) with member pair-equal q seen
... | yes _ = fresh-all seen ps
... | no _ = p ∷ fresh-all seen ps

remove-many : List Pair → List Pair → List Pair
remove-many [] remaining = remaining
remove-many (q ∷ qs) remaining = remove-many qs (remove pair-equal q remaining)

remove-many-length : ∀ qs remaining → length (remove-many qs remaining) ≤ length remaining
remove-many-length [] remaining = ≤-refl
remove-many-length (q ∷ qs) remaining = ≤-trans
  (remove-many-length qs (remove pair-equal q remaining)) (remove-length pair-equal q remaining)

remove-many-shorter : ∀ q qs remaining → q ∈ˡ remaining → length (remove-many (q ∷ qs) remaining) < length remaining
remove-many-shorter q qs remaining h = ≤-trans
  (s≤s (remove-many-length qs (remove pair-equal q remaining))) (remove-shorter pair-equal q remaining h)

remove-many-preserve : ∀ qs remaining {p} → (p ∈ˡ qs → ⊥) → p ∈ˡ remaining → p ∈ˡ remove-many qs remaining
remove-many-preserve [] remaining absent h = h
remove-many-preserve (q ∷ qs) remaining absent h = remove-many-preserve qs _
  (λ p → absent (there p)) (remove-preserve pair-equal q remaining (λ eq → absent (here eq)) h)

advance-cover : ∀ seen remaining qs → Cover seen remaining → Cover (fresh seen qs ++ seen) (remove-many (fresh seen qs) remaining)
advance-cover seen remaining qs cover p with member pair-equal p (fresh seen qs)
... | yes h = inj₁ (append-left seen h)
... | no absent with cover p
...   | inj₁ h = inj₁ (append-right (fresh seen qs) h)
...   | inj₂ h = inj₂ (remove-many-preserve (fresh seen qs) remaining absent h)

into-seen : ∀ {seen qs q} → Known seen qs q → q ∈ˡ (fresh seen qs ++ seen)
into-seen {seen} {qs} (inj₁ h) = append-right (fresh seen qs) h
into-seen {seen} {qs} (inj₂ h) with fresh-cover seen h
... | inj₁ p = append-right (fresh seen qs) p
... | inj₂ p = append-left seen p

neighbors : List Pair → List Pair
neighbors qs = concatMap (λ q → map (successor q) alphabet) qs

neighbor-member : ∀ {qs q} → q ∈ˡ qs → ∀ {a} → a ∈ˡ alphabet → successor q a ∈ˡ neighbors qs
neighbor-member {qs = q ∷ qs} (here refl) h = append-left (neighbors qs) (map-member (successor q) h)
neighbor-member {qs = q ∷ qs} (there k) h = append-right (map (successor q) alphabet) (neighbor-member k h)

snoc-length : ∀ (x : List A) a → length (x ++ (a ∷ [])) ≡ suc (length x)
snoc-length [] a = refl
snoc-length (b ∷ x) a = cong suc (snoc-length x a)

extend-path : ∀ {start depth q} → Path start depth q → ∀ a → a ∈ˡ alphabet → Path start (suc depth) (successor q a)
extend-path {start} {depth} {q} (path x endpoint distance supported) a h = path (x ++ (a ∷ []))
  (trans (run-append start x (a ∷ [])) (cong (λ q → successor q a) endpoint))
  (trans (snoc-length x a) (cong suc distance)) (all-append supported (h ∷ []))

neighbor-paths : ∀ {start depth qs} → All (Path start depth) qs → All (Path start (suc depth)) (neighbors qs)
neighbor-paths [] = []
neighbor-paths (p ∷ ps) = all-append (each alphabet (λ h → h)) (neighbor-paths ps)
  where
  each : ∀ symbols → (∀ {a} → a ∈ˡ symbols → a ∈ˡ alphabet) → All (Path _ _) (map (successor _) symbols)
  each [] cover = []
  each (a ∷ symbols) cover = extend-path p a (cover (here refl)) ∷ each symbols (λ h → cover (there h))

refute-good : ∀ {start x} → Good (run-pair start x) → Separates start x → ⊥
refute-good eq (inj₁ (p , nq)) = nq (trans (sym eq) p)
refute-good eq (inj₂ (q , np)) = np (trans eq q)

check : ∀ start depth qs → All (Path start depth) qs →
  All Good qs ⊎ (Σ (List A) λ x → Separates start x × (length x ≡ depth) × All (λ a → a ∈ˡ alphabet) x)
check start depth [] [] = inj₁ []
check start depth (q ∷ qs) (path x refl distance supported ∷ paths) with output m (proj₁ q) in ep | output n (proj₂ q) in eq
... | true | false = inj₂ (x , inj₁ (ep , (λ h → false-true (trans (sym eq) h))) , distance , supported)
  where
  false-true : false ≡ true → ⊥
  false-true ()
... | false | true = inj₂ (x , inj₂ (eq , (λ h → false-true (trans (sym ep) h))) , distance , supported)
  where
  false-true : false ≡ true → ⊥
  false-true ()
... | true | true with check start depth qs paths
...   | inj₁ goods = inj₁ (trans ep (sym eq) ∷ goods)
...   | inj₂ w = inj₂ w
check start depth (q ∷ qs) (path x refl distance supported ∷ paths) | false | false with check start depth qs paths
... | inj₁ goods = inj₁ (trans ep (sym eq) ∷ goods)
... | inj₂ w = inj₂ w

History : Pair → ℕ → List Pair → Set
History start depth seen = ∀ x → All (λ a → a ∈ˡ alphabet) x → length x < depth → run-pair start x ∈ˡ seen

letters-init : ∀ x a → All (λ b → b ∈ˡ alphabet) (x ++ (a ∷ [])) → All (λ b → b ∈ˡ alphabet) x
letters-init [] a h = []
letters-init (b ∷ x) a (h ∷ hs) = h ∷ letters-init x a hs

letters-last : ∀ x a → All (λ b → b ∈ˡ alphabet) (x ++ (a ∷ [])) → a ∈ˡ alphabet
letters-last [] a (h ∷ []) = h
letters-last (b ∷ x) a (h ∷ hs) = letters-last x a hs

history-next : ∀ {start depth seen qs} → History start depth seen → Frontier seen qs → Known seen qs start →
  History start (suc depth) (fresh seen qs ++ seen)
history-next {start} {depth} {seen} {qs} history frontier initial x letters bound with initLast x
... | [] = into-seen initial
... | prefix ∷ʳ′ a = subst (λ q → q ∈ˡ (fresh seen qs ++ seen)) (sym (run-append start prefix (a ∷ [])))
  (into-seen (proj₂ (frontier (run-pair start prefix)
    (history prefix (letters-init prefix a letters) prefix-short)) a (letters-last prefix a letters)))
  where
  prefix-short : length prefix < depth
  prefix-short with subst (λ k → k < suc depth) (snoc-length prefix a) bound
  ... | s≤s h = h

frontier-next : ∀ {seen qs} → Frontier seen qs → All Good (fresh seen qs) →
  Frontier (fresh seen qs ++ seen) (neighbors (fresh seen qs))
frontier-next {seen} {qs} frontier goods q present with append-view (fresh seen qs) present
... | inj₁ h = all-lookup h goods , λ a k → inj₂ (neighbor-member h k)
... | inj₂ h = proj₁ (frontier q h) , λ a k → inj₁ (into-seen (proj₂ (frontier q h) a k))

minimal-from-history : ∀ {start depth seen qs} {x : List A} → History start depth seen → Frontier seen qs →
  length x ≡ depth → ∀ y → All (λ a → a ∈ˡ alphabet) y → Separates start y → length x ≤ length y
minimal-from-history {start} {depth} {seen} {qs} {x} history frontier distance y letters separates with length x ≤? length y
... | yes h = h
... | no absent = ⊥-elim (refute-good {start = start} {x = y} (proj₁ (frontier _
  (history y letters (subst (length y <_) distance (≰⇒> absent))))) separates)

search : (start : Pair) → (@0 remaining : List Pair) → @0 Acc _<_ (length remaining) →
  (depth : ℕ) (seen qs : List Pair) → @0 Cover seen remaining →
  All (Path start depth) qs → Frontier seen qs → Known seen qs start → History start depth seen →
  On start ⊎ Shortest start
search start remaining (acc smaller) depth seen qs cover paths frontier initial history with fresh seen qs in ef
... | [] = inj₁ (bisimilar seen closed start (only-seen initial))
  where
  only-seen : ∀ {q} → Known seen qs q → q ∈ˡ seen
  only-seen (inj₁ h) = h
  only-seen (inj₂ h) with fresh-cover seen h
  ... | inj₁ p = p
  ... | inj₂ p with subst (_ ∈ˡ_) ef p
  ...   | ()
  closed : Closed seen
  closed q h = proj₁ (frontier q h) , λ a k → only-seen (proj₂ (frontier q h) a k)
... | q ∷ rest with check start depth (q ∷ rest) (subst (All (Path start depth)) ef (fresh-all seen paths))
...   | inj₂ (x , witness , distance , supported) = inj₂
  (shortest x witness supported (minimal-from-history {start = start} {depth = depth} {seen = seen} {qs = qs} {x = x} history frontier distance))
...   | inj₁ goods = search start (remove-many (fresh seen qs) remaining)
  (smaller (subst (λ fs → length (remove-many fs remaining) < length remaining) (sym ef)
    (remove-many-shorter q rest remaining present)))
  (suc depth) (fresh seen qs ++ seen) (neighbors (fresh seen qs)) (advance-cover seen remaining qs cover)
  (neighbor-paths (fresh-all seen paths))
  (frontier-next frontier (subst (All Good) (sym ef) goods))
  (inj₁ (into-seen initial)) (history-next history frontier initial)
  where
  @0 present : q ∈ˡ remaining
  present with cover q
  ... | inj₂ h = h
  ... | inj₁ h = ⊥-elim (proj₂ (fresh-member seen {qs = qs} (subst (q ∈ˡ_) (sym ef) (here refl))) h)

decide : ∀ start → On start ⊎ Shortest start
decide start = search start universe (<-wellFounded (length universe)) zero [] (start ∷ [])
  (λ q → inj₂ (universe-complete q)) (path [] refl refl [] ∷ []) (λ q ()) (inj₂ (here refl))
  (λ x letters ())
