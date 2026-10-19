{-# OPTIONS --safe --without-K #-}

module Rumus.Print where

open import Data.Char.Base using (Char)
open import Data.String.Base using (String; _++_; fromChar)
open import Data.Nat.Base using (ℕ; zero; suc)
open import Rumus.Regex

literal-text : Char → String
literal-text '(' = "\\("
literal-text ')' = "\\)"
literal-text '|' = "\\|"
literal-text '*' = "\\*"
literal-text '@' = "\\@"
literal-text '#' = "\\#"
literal-text '\\' = "\\\\"
literal-text a = fromChar a

wrap : ℕ → ℕ → String → String
wrap zero inner s = s
wrap (suc outer) zero s = "(" ++ s ++ ")"
wrap (suc outer) (suc inner) s = wrap outer inner s

render : ℕ → Regex Char → String
render outer ∅ = "#"
render outer ε = "@"
render outer (lit a) = literal-text a
render outer (r ∪ s) = wrap outer 1 (render 1 r ++ "|" ++ render 1 s)
render outer (r ∙ s) = wrap outer 2 (render 2 r ++ render 2 s)
render outer (star r) = wrap outer 3 (render 3 r ++ "*")

print-regex : Regex Char → String
print-regex = render 0
