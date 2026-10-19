{-# OPTIONS --safe --without-K #-}

module Rumus.Cardinality where

open import Data.List.Base using (List; []; _∷_; _++_; map; length)
open import Data.Product.Base using (_,_)
open import Data.Nat.Base using (ℕ; suc; _+_; _*_; _^_)
open import Data.Nat.Properties using (+-identityʳ)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; sym; cong; cong₂)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Rumus.Regex
open import Rumus.Finite using (selections; cartesian; skip; take)
import Rumus.Residual
import Rumus.Automaton

occurrences : ∀ {A : Set} → Regex A → ℕ
occurrences ∅ = 0
occurrences ε = 0
occurrences (lit a) = 1
occurrences (r ∪ s) = occurrences r + occurrences s
occurrences (r ∙ s) = occurrences r + occurrences s
occurrences (star r) = occurrences r

state-bound : ∀ {A : Set} → Regex A → ℕ
state-bound r = suc (2 ^ occurrences r)

pair-bound : ∀ {A : Set} → Regex A → Regex A → ℕ
pair-bound r s = state-bound r * state-bound s

length-append : ∀ {X : Set} (xs ys : List X) → length (xs ++ ys) ≡ length xs + length ys
length-append [] ys = refl
length-append (_ ∷ xs) ys = cong suc (length-append xs ys)

length-map : ∀ {X Y : Set} (f : X → Y) xs → length (map f xs) ≡ length xs
length-map f [] = refl
length-map f (_ ∷ xs) = cong suc (length-map f xs)

length-selections : ∀ {X : Set} (xs : List X) → length (selections xs) ≡ 2 ^ length xs
length-selections [] = refl
length-selections (x ∷ xs) = trans
  (length-append (map skip (selections xs)) (map take (selections xs)))
  (trans (cong₂ _+_ (trans (length-map skip (selections xs)) (length-selections xs))
    (trans (length-map take (selections xs)) (length-selections xs)))
    (cong ((2 ^ length xs) +_) (sym (+-identityʳ (2 ^ length xs)))))

length-cartesian : ∀ {X Y : Set} (xs : List X) (ys : List Y) → length (cartesian xs ys) ≡ length xs * length ys
length-cartesian [] ys = refl
length-cartesian (x ∷ xs) ys = trans (length-append (map (x ,_) ys) (cartesian xs ys))
  (cong₂ _+_ (length-map (x ,_) ys) (length-cartesian xs ys))

module Counts {A : Set} (_≟_ : DecidableEquality A) where
  open Rumus.Residual _≟_ using (positions; ul; ur; cl; cr; st)

  positions-size : ∀ r → length (positions r) ≡ occurrences r
  positions-size ∅ = refl
  positions-size ε = refl
  positions-size (lit a) = refl
  positions-size (r ∪ s) = trans (length-append (map ul (positions r)) (map ur (positions s)))
    (cong₂ _+_ (trans (length-map ul (positions r)) (positions-size r))
      (trans (length-map ur (positions s)) (positions-size s)))
  positions-size (r ∙ s) = trans (length-append (map cl (positions r)) (map cr (positions s)))
    (cong₂ _+_ (trans (length-map cl (positions r)) (positions-size r))
      (trans (length-map cr (positions s)) (positions-size s)))
  positions-size (star r) = trans (length-map st (positions r)) (positions-size r)

  states-size : ∀ r → length (Rumus.Automaton.states _≟_ r) ≡ state-bound r
  states-size r = cong suc (trans (length-map (Rumus.Automaton.residual {_≟_ = _≟_} {r = r}) (selections (positions r)))
    (trans (length-selections (positions r)) (cong (2 ^_) (positions-size r))))

  pairs-size : ∀ r s → length (cartesian (Rumus.Automaton.states _≟_ r) (Rumus.Automaton.states _≟_ s)) ≡ pair-bound r s
  pairs-size r s = trans (length-cartesian (Rumus.Automaton.states _≟_ r) (Rumus.Automaton.states _≟_ s))
    (cong₂ _*_ (states-size r) (states-size s))
