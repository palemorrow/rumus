{-# OPTIONS --safe --without-K #-}

module Rumus.Parser where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (ℕ; suc)
open import Data.Product.Base using (_×_; _,_)
open import Data.String.Base using (String; toList)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Rumus.Regex
open import Rumus.Parser.Token
open import Rumus.Parser.Syntax public

record Error : Set where
  constructor error
  field
    offset : ℕ
    message : String


reduce : Operator → Operands → String ⊎ Operands
reduce choice (s ∷ r ∷ rs) = inj₂ ((r ∪ s) ∷ rs)
reduce sequence (s ∷ r ∷ rs) = inj₂ ((r ∙ s) ∷ rs)
reduce _ _ = inj₁ "missing operand"

push-sequence : Stack → Operands → String ⊎ (Stack × Operands)
push-sequence (sequence ∷ ops) rs with reduce sequence rs
... | inj₁ e = inj₁ e
... | inj₂ ss = push-sequence ops ss
push-sequence ops rs = inj₂ (sequence ∷ ops , rs)

push-choice : Stack → Operands → String ⊎ (Stack × Operands)
push-choice [] rs = inj₂ (choice ∷ [] , rs)
push-choice (group ∷ ops) rs = inj₂ (choice ∷ group ∷ ops , rs)
push-choice (choice ∷ ops) rs with reduce choice rs
... | inj₁ e = inj₁ e
... | inj₂ ss = push-choice ops ss
push-choice (sequence ∷ ops) rs with reduce sequence rs
... | inj₁ e = inj₁ e
... | inj₂ ss = push-choice ops ss

close : Stack → Operands → String ⊎ (Stack × Operands)
close [] rs = inj₁ "unmatched closing parenthesis"
close (group ∷ ops) rs = inj₂ (ops , rs)
close (choice ∷ ops) rs with reduce choice rs
... | inj₁ e = inj₁ e
... | inj₂ ss = close ops ss
close (sequence ∷ ops) rs with reduce sequence rs
... | inj₁ e = inj₁ e
... | inj₂ ss = close ops ss

finish : Stack → Operands → String ⊎ Regex Char
finish [] (r ∷ []) = inj₂ r
finish [] _ = inj₁ "expected expression"
finish (group ∷ ops) rs = inj₁ "unclosed parenthesis"
finish (choice ∷ ops) rs with reduce choice rs
... | inj₁ e = inj₁ e
... | inj₂ ss = finish ops ss
finish (sequence ∷ ops) rs with reduce sequence rs
... | inj₁ e = inj₁ e
... | inj₂ ss = finish ops ss

prepare : Bool → Stack → Operands → String ⊎ (Stack × Operands)
prepare true ops rs = inj₂ (ops , rs)
prepare false ops rs = push-sequence ops rs


parse-loop : List Char → ℕ → Bool → Stack → Operands → Error ⊎ Regex Char
parse-loop [] n true ops rs = inj₁ (error n "expected expression")
parse-loop [] n false ops rs with finish ops rs
... | inj₁ e = inj₁ (error n e)
... | inj₂ r = inj₂ r
parse-loop (c ∷ cs) n expect ops rs with kind c | expect
... | opening | need with prepare need ops rs
...   | inj₁ e = inj₁ (error n e)
...   | inj₂ (os , ss) = parse-loop cs (suc n) true (group ∷ os) ss
parse-loop (c ∷ cs) n expect ops rs | closing | true = inj₁ (error n "expected expression before closing parenthesis")
parse-loop (c ∷ cs) n expect ops rs | closing | false with close ops rs
... | inj₁ e = inj₁ (error n e)
... | inj₂ (os , ss) = parse-loop cs (suc n) false os ss
parse-loop (c ∷ cs) n expect ops rs | alternation | true = inj₁ (error n "missing left operand of union")
parse-loop (c ∷ cs) n expect ops rs | alternation | false with push-choice ops rs
... | inj₁ e = inj₁ (error n e)
... | inj₂ (os , ss) = parse-loop cs (suc n) true os ss
parse-loop (c ∷ cs) n expect ops rs | repetition | true = inj₁ (error n "star requires an operand")
parse-loop (c ∷ cs) n expect ops [] | repetition | false = inj₁ (error n "star requires an operand")
parse-loop (c ∷ cs) n expect ops (r ∷ rs) | repetition | false = parse-loop cs (suc n) false ops (star r ∷ rs)
parse-loop (c ∷ []) n expect ops rs | escaping | need = inj₁ (error n "trailing escape")
parse-loop (c ∷ d ∷ cs) n expect ops rs | escaping | need with prepare need ops rs
... | inj₁ e = inj₁ (error n e)
... | inj₂ (os , ss) = parse-loop cs (suc (suc n)) false os (lit d ∷ ss)
parse-loop (c ∷ cs) n expect ops rs | ordinary | need with prepare need ops rs
... | inj₁ e = inj₁ (error n e)
... | inj₂ (os , ss) = parse-loop cs (suc n) false os (atom c ∷ ss)

parse-chars : List Char → Error ⊎ Regex Char
parse-chars cs = parse-loop cs 0 true [] []

parse : String → Error ⊎ Regex Char
parse s = parse-chars (toList s)
