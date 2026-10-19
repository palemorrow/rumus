{-# OPTIONS --safe --without-K #-}

module Rumus.Algebra where

open import Data.List.Base using (List; []; _∷_; _++_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; cong; sym)
open import Rumus.Regex
open import Rumus.Language

private
  variable
    A : Set
    r s t u : Regex A

append-assoc : ∀ {A : Set} (x y z : List A) → (x ++ y) ++ z ≡ x ++ (y ++ z)
append-assoc [] y z = refl
append-assoc (a ∷ x) y z = cong (a ∷_) (append-assoc x y z)

append-empty : ∀ {A : Set} (x : List A) → x ++ [] ≡ x
append-empty [] = refl
append-empty (a ∷ x) = cong (a ∷_) (append-empty x)

union-cong : r ≈ s → t ≈ u → (r ∪ t) ≈ (s ∪ u)
union-cong e f =
  (λ { (left p) → left (proj₁ e p) ; (right p) → right (proj₁ f p) }) ,
  (λ { (left p) → left (proj₂ e p) ; (right p) → right (proj₂ f p) })

concat-cong : r ≈ s → t ≈ u → (r ∙ t) ≈ (s ∙ u)
concat-cong e f =
  (λ { (concat p q) → concat (proj₁ e p) (proj₁ f q) }) ,
  (λ { (concat p q) → concat (proj₂ e p) (proj₂ f q) })

star-map : (∀ {x} → x ∈ r → x ∈ s) → ∀ {x} → x ∈ star r → x ∈ star s
star-map f stop = stop
star-map f (repeat p q) = repeat (f p) (star-map f q)

star-cong : r ≈ s → star r ≈ star s
star-cong e = star-map (proj₁ e) , star-map (proj₂ e)

union-emptyˡ : (∅ ∪ r) ≈ r
union-emptyˡ = (λ { (left ()) ; (right p) → p }) , right

union-emptyʳ : (r ∪ ∅) ≈ r
union-emptyʳ = (λ { (left p) → p ; (right ()) }) , left

union-idem : (r ∪ r) ≈ r
union-idem = (λ { (left p) → p ; (right p) → p }) , left

union-comm : (r ∪ s) ≈ (s ∪ r)
union-comm =
  (λ { (left p) → right p ; (right p) → left p }) ,
  (λ { (left p) → right p ; (right p) → left p })

union-assoc : ((r ∪ s) ∪ t) ≈ (r ∪ (s ∪ t))
union-assoc =
  (λ { (left (left p)) → left p ; (left (right p)) → right (left p) ;
       (right p) → right (right p) }) ,
  (λ { (left p) → left (left p) ; (right (left p)) → left (right p) ;
       (right (right p)) → right p })

concat-zeroˡ : (∅ ∙ r) ≈ ∅
concat-zeroˡ = (λ { (concat () q) }) , (λ ())

concat-zeroʳ : (r ∙ ∅) ≈ ∅
concat-zeroʳ = (λ { (concat p ()) }) , (λ ())

concat-unitˡ : (ε ∙ r) ≈ r
concat-unitˡ = (λ { (concat empty p) → p }) , concat empty

concat-unitʳ : (r ∙ ε) ≈ r
concat-unitʳ {x = x} =
  (λ { (concat {x = x} p empty) → transport (sym (append-empty x)) p }) ,
  (λ p → transport (append-empty x) (concat p empty))

star-append : ∀ {x y} → x ∈ star r → y ∈ star r → (x ++ y) ∈ star r
star-append stop q = q
star-append (repeat {x = x} {y} p ps) q =
  transport (sym (append-assoc x y _)) (repeat p (star-append ps q))

star-flatten : ∀ {x} → x ∈ star (star r) → x ∈ star r
star-flatten stop = stop
star-flatten (repeat p q) = star-append p (star-flatten q)

star-idem : star (star r) ≈ star r
star-idem {x = x} = star-flatten , (λ p → transport (append-empty x) (repeat p stop))

star-empty : star (∅ {A}) ≈ ε
star-empty = (λ { stop → empty ; (repeat () q) }) , (λ { empty → stop })

star-epsilon : star (ε {A}) ≈ ε
star-epsilon = collapse , (λ { empty → stop })
  where
  collapse : ∀ {x} → x ∈ star ε → x ∈ ε
  collapse stop = empty
  collapse (repeat empty q) = collapse q

distribute : ((r ∪ s) ∙ t) ≈ ((r ∙ t) ∪ (s ∙ t))
distribute =
  (λ { (concat (left p) q) → left (concat p q) ;
       (concat (right p) q) → right (concat p q) }) ,
  (λ { (left (concat p q)) → concat (left p) q ;
       (right (concat p q)) → concat (right p) q })
