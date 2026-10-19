{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Residual {A : Set} (_≟_ : DecidableEquality A) where

open import Data.List.Base using (List; []; _∷_; _++_; map)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (refl)
open import Relation.Nullary using (yes; no)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Algebra
open import Rumus.Nullable
open import Rumus.Derivative _≟_
open import Rumus.Join
open import Rumus.Finite
open import Data.List.Relation.Unary.Any using (here)
open import Relation.Nullary using (Dec)

data Position : Regex A → Set where
  hit : ∀ {a} → Position (lit a)
  ul : ∀ {r s} → Position r → Position (r ∪ s)
  ur : ∀ {r s} → Position s → Position (r ∪ s)
  cl : ∀ {r s} → Position r → Position (r ∙ s)
  cr : ∀ {r s} → Position s → Position (r ∙ s)
  st : ∀ {r} → Position r → Position (star r)

body : ∀ {r} → Position r → Regex A
body hit = ε
body (ul p) = body p
body (ur p) = body p
body (cl {s = s} p) = body p ∙ s
body (cr p) = body p
body (st {r} p) = body p ∙ star r

positions : (r : Regex A) → List (Position r)
positions ∅ = []
positions ε = []
positions (lit a) = hit ∷ []
positions (r ∪ s) = map ul (positions r) ++ map ur (positions s)
positions (r ∙ s) = map cl (positions r) ++ map cr (positions s)
positions (star r) = map st (positions r)

positions-complete : ∀ {r} (p : Position r) → p ∈ˡ positions r
positions-complete hit = here refl
positions-complete (ul {s = s} p) = append-left (map ur (positions s)) (map-member ul (positions-complete p))
positions-complete (ur {r} p) = append-right (map ul (positions r)) (map-member ur (positions-complete p))
positions-complete (cl {s = s} p) = append-left (map cr (positions s)) (map-member cl (positions-complete p))
positions-complete (cr {r} p) = append-right (map cl (positions r)) (map-member cr (positions-complete p))
positions-complete (st p) = map-member st (positions-complete p)

position-equal : ∀ {r} → DecidableEquality (Position r)
position-equal hit hit = yes refl
position-equal (ul p) (ur q) = no (λ ())
position-equal (ur p) (ul q) = no (λ ())
position-equal (cl p) (cr q) = no (λ ())
position-equal (cr p) (cl q) = no (λ ())
position-equal (ul p) (ul q) with position-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
position-equal (ur p) (ur q) with position-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
position-equal (cl p) (cl q) with position-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
position-equal (cr p) (cr q) with position-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }
position-equal (st p) (st q) with position-equal p q
... | yes refl = yes refl
... | no n = no λ { refl → n refl }

first : (r : Regex A) → A → List (Position r)
first ∅ a = []
first ε a = []
first (lit b) a with a ≟ b
... | yes _ = hit ∷ []
... | no _ = []
first (r ∪ s) a = map ul (first r a) ++ map ur (first s a)
first (r ∙ s) a with nullable r
... | yes _ = map cl (first r a) ++ map cr (first s a)
... | no _ = map cl (first r a)
first (star r) a = map st (first r a)

first-correct : ∀ r a → join body (first r a) ≈ derive a r
first-correct ∅ a = ≈-refl
first-correct ε a = ≈-refl
first-correct (lit b) a with a ≟ b
... | yes _ = union-emptyʳ
... | no _ = ≈-refl
first-correct (r ∪ s) a =
  ≈-trans (join-append body (map ul (first r a)) (map ur (first s a)))
  (union-cong (≈-trans (join-map-correct body ul (first r a)) (first-correct r a))
              (≈-trans (join-map-correct body ur (first s a)) (first-correct s a)))
first-correct (r ∙ s) a with nullable r
... | yes _ =
  ≈-trans (join-append body (map cl (first r a)) (map cr (first s a)))
  (union-cong (≈-trans (join-map-correct body cl (first r a))
    (≈-trans (join-concat body (first r a) s) (concat-cong (first-correct r a) ≈-refl)))
    (≈-trans (join-map-correct body cr (first s a)) (first-correct s a)))
... | no _ = ≈-trans (join-map-correct body cl (first r a))
  (≈-trans (join-concat body (first r a) s) (concat-cong (first-correct r a) ≈-refl))
first-correct (star r) a = ≈-trans (join-map-correct body st (first r a))
  (≈-trans (join-concat body (first r a) (star r)) (concat-cong (first-correct r a) ≈-refl))

next : ∀ {r} → Position r → A → List (Position r)
next hit a = []
next (ul p) a = map ul (next p a)
next (ur p) a = map ur (next p a)
next (cl {s = s} p) a with nullable (body p)
... | yes _ = map cl (next p a) ++ map cr (first s a)
... | no _ = map cl (next p a)
next (cr p) a = map cr (next p a)
next (st {r} p) a with nullable (body p)
... | yes _ = map st (next p a) ++ map st (first r a)
... | no _ = map st (next p a)

next-correct : ∀ {r} (p : Position r) a → join body (next p a) ≈ derive a (body p)
next-correct hit a = ≈-refl
next-correct (ul p) a = ≈-trans (join-map-correct body ul (next p a)) (next-correct p a)
next-correct (ur p) a = ≈-trans (join-map-correct body ur (next p a)) (next-correct p a)
next-correct (cl {s = s} p) a with nullable (body p)
... | yes _ =
  ≈-trans (join-append body (map cl (next p a)) (map cr (first s a)))
  (union-cong (≈-trans (join-map-correct body cl (next p a))
    (≈-trans (join-concat body (next p a) s) (concat-cong (next-correct p a) ≈-refl)))
    (≈-trans (join-map-correct body cr (first s a)) (first-correct s a)))
... | no _ = ≈-trans (join-map-correct body cl (next p a))
  (≈-trans (join-concat body (next p a) s) (concat-cong (next-correct p a) ≈-refl))
next-correct (cr p) a = ≈-trans (join-map-correct body cr (next p a)) (next-correct p a)
next-correct (st {r} p) a with nullable (body p)
... | yes _ =
  ≈-trans (join-append body (map st (next p a)) (map st (first r a)))
  (union-cong (≈-trans (join-map-correct body st (next p a))
    (≈-trans (join-concat body (next p a) (star r)) (concat-cong (next-correct p a) ≈-refl)))
    (≈-trans (join-map-correct body st (first r a))
    (≈-trans (join-concat body (first r a) (star r)) (concat-cong (first-correct r a) ≈-refl))))
... | no _ = ≈-trans (join-map-correct body st (next p a))
  (≈-trans (join-concat body (next p a) (star r)) (concat-cong (next-correct p a) ≈-refl))
