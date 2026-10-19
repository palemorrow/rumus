{-# OPTIONS --safe --without-K #-}

module Rumus.Command where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.List.Base using (List; []; _∷_)
open import Agda.Builtin.String using () renaming (primShowNat to show)
open import Data.String.Base using (String; _++_; toList; fromList)
open import Data.Sum.Base using (inj₁; inj₂)
open import Rumus.Regex
open import Rumus.Parser
open import Rumus.Print
open import Rumus.Characters

record Response : Set where
  constructor response
  field
    success : Bool
    text : String

bool-text : Bool → String
bool-text true = "true"
bool-text false = "false"

parse-error : Error → Response
parse-error e = response false ("parse error at offset " ++ show (Error.offset e) ++ ": " ++ Error.message e)

trace : Regex Char → List Char → String
trace r [] = print-regex r ++ "\nnullable: " ++ bool-text (accepts r [])
trace r (a ∷ x) = print-regex r ++ "\n  d/" ++ literal-text a ++ "\n" ++ trace (step a r) x

batch : ∀ {r} → Compiled r → List String → String
batch program [] = ""
batch program (x ∷ []) = bool-text (compiled-accepts program (toList x))
batch program (x ∷ xs) = bool-text (compiled-accepts program (toList x)) ++ "\n" ++ batch program xs

usage : String
usage = "usage: rumus match REGEX INPUT\n       rumus match-many REGEX INPUT...\n       rumus equivalent REGEX REGEX\n       rumus normalize REGEX\n       rumus serialize REGEX\n       rumus trace REGEX INPUT\nsyntax: # empty, @ epsilon, | union, juxtaposition, *, (), \\ escape"

command : List String → Response
command ("match" ∷ regex-text ∷ input ∷ []) with parse regex-text
... | inj₁ e = parse-error e
... | inj₂ r = response true (bool-text (accepts (normalize r) (toList input)))
command ("match-many" ∷ regex-text ∷ input ∷ inputs) with parse regex-text
... | inj₁ e = parse-error e
... | inj₂ r = response true (batch (compile (normalize r)) (input ∷ inputs))
command ("equivalent" ∷ lhs ∷ rhs ∷ []) with parse lhs | parse rhs
... | inj₁ e | _ = parse-error e
... | inj₂ _ | inj₁ e = parse-error e
... | inj₂ r | inj₂ s with equivalence r s
...   | equivalent _ = response true "equivalent"
...   | different [] _ = response true "not equivalent\ncounterexample: @ (empty string)"
...   | different x _ = response true ("not equivalent\ncounterexample: " ++ fromList x)
command ("normalize" ∷ regex-text ∷ []) with parse regex-text
... | inj₁ e = parse-error e
... | inj₂ r = response true (print-regex (normalize r))
command ("serialize" ∷ regex-text ∷ []) with parse regex-text
... | inj₁ e = parse-error e
... | inj₂ r = response true (fromList (print-chars r))
command ("trace" ∷ regex-text ∷ input ∷ []) with parse regex-text
... | inj₁ e = parse-error e
... | inj₂ r = response true (trace (normalize r) (toList input))
command ("--help" ∷ []) = response true usage
command _ = response false usage
