{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)
open import Rumus.Regex using (Regex)

module Rumus.CachedAutomaton {A : Set} (_≟_ : DecidableEquality A) (r : Regex A) where

open import Data.Bool.Base using (Bool; false; _∨_)
open import Data.List.Base using (List; []; _∷_; concatMap)
open import Data.Product.Base using (_,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; cong; cong₂; subst; sym)
open import Relation.Nullary using (does; yes; no)
open import Rumus.Regex
open import Rumus.Language using (_∈_)
open import Rumus.Nullable
open import Rumus.Join
open import Rumus.Support using (symbols)
open import Rumus.Finite using (Selection; selected; select; unique)
open import Rumus.Table
import Rumus.Automaton
open import Rumus.Residual _≟_ using (Position; positions; position-equal; first; next; body)
import Rumus.Machine as M

module Base = Rumus.Automaton _≟_ r
open Base public using (State; initial; residual; equal; states; states-complete; denote)

alphabet : List A
alphabet = unique _≟_ (symbols r)

record Tables : Set where
  constructor tables
  field
    first-row : Table A (List (Position r))
    next-rows : Table (Position r) (Table A (List (Position r)))
    final-row : Table (Position r) Bool
    initial-final : Bool

prepared : Tables
prepared = tables (tabulate alphabet (first r))
  (tabulate (positions r) (λ p → tabulate alphabet (next p)))
  (tabulate (positions r) (λ p → does (nullable (body p)))) (does (nullable r))

next-cached : Position r → A → List (Position r)
next-cached p = lookup _≟_
  (lookup position-equal (Tables.next-rows prepared) (λ p → tabulate alphabet (next p)) p) (next p)

next-correct : ∀ p a → next-cached p a ≡ next p a
next-correct p a = trans
  (cong (λ row → lookup _≟_ row (next p) a)
    (lookup-correct position-equal (positions r) (λ p → tabulate alphabet (next p)) p))
  (lookup-correct _≟_ alphabet (next p) a)

transition : Tables → State → A → State
transition cache initial a = residual (select position-equal (positions r)
  (lookup _≟_ (Tables.first-row cache) (first r) a))
transition cache (residual q) a = residual (select position-equal (positions r)
  (concatMap (λ p → lookup _≟_
    (lookup position-equal (Tables.next-rows cache) (λ p → tabulate alphabet (next p)) p) (next p) a) (selected q)))

step : State → A → State
step = transition prepared

next-list-correct : ∀ ps a → concatMap (λ p → next-cached p a) ps ≡ concatMap (λ p → next p a) ps
next-list-correct [] a = refl
next-list-correct (p ∷ ps) a = cong₂ Data.List.Base._++_ (next-correct p a) (next-list-correct ps a)

step-correct : ∀ q a → step q a ≡ Base.step q a
step-correct initial a = cong (λ ps → residual (select position-equal (positions r) ps))
  (lookup-correct _≟_ alphabet (first r) a)
step-correct (residual q) a = cong (λ ps → residual (select position-equal (positions r) ps)) (next-list-correct (selected q) a)

finals : Tables → List (Position r) → Bool
finals cache [] = false
finals cache (p ∷ ps) = lookup position-equal (Tables.final-row cache) (λ p → does (nullable (body p))) p ∨ finals cache ps

nullable-union : ∀ (s t : Regex A) → does (nullable (s ∪ t)) ≡ (does (nullable s) ∨ does (nullable t))
nullable-union s t with nullable s | nullable t
... | yes _ | yes _ = refl
... | yes _ | no _ = refl
... | no _ | yes _ = refl
... | no _ | no _ = refl

finals-correct : ∀ ps → finals prepared ps ≡ does (nullable (join body ps))
finals-correct [] = refl
finals-correct (p ∷ ps) = trans
  (cong₂ _∨_ (lookup-correct position-equal (positions r) (λ p → does (nullable (body p))) p) (finals-correct ps))
  (sym (nullable-union (body p) (join body ps)))

observe : Tables → State → Bool
observe cache initial = Tables.initial-final cache
observe cache (residual q) = finals cache (selected q)

output-correct : ∀ q → observe prepared q ≡ M.output Base.machine q
output-correct initial = refl
output-correct (residual q) = finals-correct (selected q)

machine : M.Machine A
machine = record
  { State = State
  ; equal = equal
  ; states = states
  ; complete = states-complete
  ; step = transition prepared
  ; output = observe prepared
  }

run-correct : ∀ q x → M.run machine q x ≡ M.run Base.machine q x
run-correct q [] = refl
run-correct q (a ∷ x) = trans (run-correct (step q a) x) (cong (λ q → M.run Base.machine q x) (step-correct q a))

accept-correct : ∀ q x → M.output machine (M.run machine q x) ≡ M.output Base.machine (M.run Base.machine q x)
accept-correct q x = trans (output-correct (M.run machine q x)) (cong (M.output Base.machine) (run-correct q x))

accept-sound : ∀ q x → M.Accept machine q x → x ∈ denote q
accept-sound q x proof = Base.accept-sound q x (trans (sym (accept-correct q x)) proof)

accept-complete : ∀ q x → x ∈ denote q → M.Accept machine q x
accept-complete q x proof = trans (accept-correct q x) (Base.accept-complete q x proof)
