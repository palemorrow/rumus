{-# OPTIONS --safe --without-K #-}

open import Relation.Binary.Definitions using (DecidableEquality)

module Rumus.Compiled {A : Set} (_≟_ : DecidableEquality A) where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Empty using (⊥-elim)
open import Data.List.Base using (List)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; trans; sym)
open import Relation.Nullary using (Dec; yes; no; does)
open import Rumus.Regex
open import Rumus.Language
import Rumus.Machine as M
import Rumus.CachedAutomaton

record Compiled (r : Regex A) : Set₁ where
  field
    automaton : M.Machine A
    initial : M.State automaton
    sound : ∀ x → M.Accept automaton initial x → x ∈ r
    complete : ∀ x → x ∈ r → M.Accept automaton initial x

compile : (r : Regex A) → Compiled r
compile r = record
  { automaton = Cached.machine
  ; initial = Cached.initial
  ; sound = Cached.accept-sound Cached.initial
  ; complete = Cached.accept-complete Cached.initial
  }
  where module Cached = Rumus.CachedAutomaton _≟_ r

start : ∀ {r} (program : Compiled r) → M.State (Compiled.automaton program)
start = Compiled.initial

advance : ∀ {r} (program : Compiled r) → M.State (Compiled.automaton program) → A → M.State (Compiled.automaton program)
advance program = M.step (Compiled.automaton program)

finish : ∀ {r} (program : Compiled r) → M.State (Compiled.automaton program) → Bool
finish program = M.output (Compiled.automaton program)

compiled-match : ∀ {r} → Compiled r → (x : List A) → Dec (x ∈ r)
compiled-match program x with finish program (M.run (Compiled.automaton program) (start program) x) in eq
... | true = yes (Compiled.sound program x eq)
... | false = no λ p → false-true (trans (sym eq) (Compiled.complete program x p))
  where
  false-true : false ≡ true → Data.Empty.⊥
  false-true ()

compiled-accepts : ∀ {r} → Compiled r → List A → Bool
compiled-accepts program x = does (compiled-match program x)

compiled-sound : ∀ {r} (program : Compiled r) x → compiled-accepts program x ≡ true → x ∈ r
compiled-sound program x with compiled-match program x
... | yes p = λ _ → p
... | no _ = λ ()

compiled-complete : ∀ {r} (program : Compiled r) x → x ∈ r → compiled-accepts program x ≡ true
compiled-complete program x p with compiled-match program x
... | yes _ = refl
... | no n = ⊥-elim (n p)
