{-# OPTIONS --safe --without-K #-}

module Rumus.Parser.Grammar where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_)
open import Rumus.Regex
open import Rumus.Parser.Syntax using (Stack; Operands; Operator; group; choice; sequence; atom)
open import Rumus.Parser.Token

data Sequence : Stack → Operands → Stack → Operands → Set where
  empty : ∀ {rs} → Sequence [] rs (sequence ∷ []) rs
  group : ∀ {ops rs} → Sequence (group ∷ ops) rs (sequence ∷ group ∷ ops) rs
  choice : ∀ {ops rs} → Sequence (choice ∷ ops) rs (sequence ∷ choice ∷ ops) rs
  reduce : ∀ {ops rs os ss r s} → Sequence ops ((r ∙ s) ∷ rs) os ss →
    Sequence (sequence ∷ ops) (s ∷ r ∷ rs) os ss

data Choice : Stack → Operands → Stack → Operands → Set where
  empty : ∀ {rs} → Choice [] rs (choice ∷ []) rs
  group : ∀ {ops rs} → Choice (group ∷ ops) rs (choice ∷ group ∷ ops) rs
  union : ∀ {ops rs os ss r s} → Choice ops ((r ∪ s) ∷ rs) os ss →
    Choice (choice ∷ ops) (s ∷ r ∷ rs) os ss
  concat : ∀ {ops rs os ss r s} → Choice ops ((r ∙ s) ∷ rs) os ss →
    Choice (sequence ∷ ops) (s ∷ r ∷ rs) os ss

data Close : Stack → Operands → Stack → Operands → Set where
  group : ∀ {ops rs} → Close (group ∷ ops) rs ops rs
  union : ∀ {ops rs os ss r s} → Close ops ((r ∪ s) ∷ rs) os ss →
    Close (choice ∷ ops) (s ∷ r ∷ rs) os ss
  concat : ∀ {ops rs os ss r s} → Close ops ((r ∙ s) ∷ rs) os ss →
    Close (sequence ∷ ops) (s ∷ r ∷ rs) os ss

data Finish : Stack → Operands → Regex Char → Set where
  done : ∀ {r} → Finish [] (r ∷ []) r
  union : ∀ {ops rs r s result} → Finish ops ((r ∪ s) ∷ rs) result →
    Finish (choice ∷ ops) (s ∷ r ∷ rs) result
  concat : ∀ {ops rs r s result} → Finish ops ((r ∙ s) ∷ rs) result →
    Finish (sequence ∷ ops) (s ∷ r ∷ rs) result

data Prepared : Bool → Stack → Operands → Stack → Operands → Set where
  first : ∀ {ops rs} → Prepared true ops rs ops rs
  next : ∀ {ops rs os ss} → Sequence ops rs os ss → Prepared false ops rs os ss

data Grammar : List Char → Bool → Stack → Operands → Regex Char → Set where
  done : ∀ {ops rs r} → Finish ops rs r → Grammar [] false ops rs r
  opening : ∀ {c cs expect ops rs os ss result} → kind c ≡ opening →
    Prepared expect ops rs os ss → Grammar cs true (group ∷ os) ss result → Grammar (c ∷ cs) expect ops rs result
  closing : ∀ {c cs ops rs os ss result} → kind c ≡ closing →
    Close ops rs os ss → Grammar cs false os ss result → Grammar (c ∷ cs) false ops rs result
  union : ∀ {c cs ops rs os ss result} → kind c ≡ alternation →
    Choice ops rs os ss → Grammar cs true os ss result → Grammar (c ∷ cs) false ops rs result
  star : ∀ {c cs ops rs r result} → kind c ≡ repetition →
    Grammar cs false ops (star r ∷ rs) result → Grammar (c ∷ cs) false ops (r ∷ rs) result
  escape : ∀ {c d cs expect ops rs os ss result} → kind c ≡ escaping →
    Prepared expect ops rs os ss → Grammar cs false os (lit d ∷ ss) result → Grammar (c ∷ d ∷ cs) expect ops rs result
  symbol : ∀ {c cs expect ops rs os ss result} → kind c ≡ ordinary →
    Prepared expect ops rs os ss → Grammar cs false os (atom c ∷ ss) result → Grammar (c ∷ cs) expect ops rs result

Parses : List Char → Regex Char → Set
Parses cs r = Grammar cs true [] [] r
