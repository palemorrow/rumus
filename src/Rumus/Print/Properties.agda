{-# OPTIONS --safe --without-K #-}

module Rumus.Print.Properties where

open import Data.Bool.Base using (false)
open import Data.Char.Base using (Char)
open import Data.List.Base using ([]; _∷_)
open import Data.Sum.Base using (inj₂)
open import Data.Product.Base using (Σ; _×_; _,_)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; sym; trans)
open import Rumus.Regex
open import Rumus.Language
open import Rumus.Print
open import Rumus.Parser using (parse-chars)
open import Rumus.Parser.Properties using (parse-chars-complete)
import Rumus.Parser.Grammar as G

emit-grammar : (r : Regex Char) → ∀ {suffix expect ops rs os ss result} →
  G.Prepared expect ops rs os ss → G.Grammar suffix false os (r ∷ ss) result →
  G.Grammar (emit r suffix) expect ops rs result
emit-grammar ∅ prep rest = G.opening refl prep (G.symbol refl G.first (G.closing refl G.group rest))
emit-grammar ε prep rest = G.opening refl prep (G.symbol refl G.first (G.closing refl G.group rest))
emit-grammar (lit c) prep rest = G.opening refl prep (G.escape refl G.first (G.closing refl G.group rest))
emit-grammar (r ∪ s) prep rest = G.opening refl prep
  (emit-grammar r G.first (G.union refl G.group (emit-grammar s G.first (G.closing refl (G.union G.group) rest))))
emit-grammar (r ∙ s) prep rest = G.opening refl prep
  (emit-grammar r G.first (emit-grammar s (G.next G.group) (G.closing refl (G.concat G.group) rest)))
emit-grammar (star r) prep rest = G.opening refl prep
  (emit-grammar r G.first (G.star refl (G.closing refl G.group rest)))

print-grammar : ∀ r → G.Parses (print-chars r) r
print-grammar r = emit-grammar r G.first (G.done G.done)

parse-print : ∀ r → parse-chars (print-chars r) ≡ inj₂ r
parse-print r = parse-chars-complete (print-chars r) (print-grammar r)

parser-printer : ∀ cs {r} → parse-chars cs ≡ inj₂ r → parse-chars (print-chars r) ≡ parse-chars cs
parser-printer cs {r} proof = trans (parse-print r) (sym proof)

printed-language : ∀ r → Σ (Regex Char) λ s → (parse-chars (print-chars r) ≡ inj₂ s) × (r ≈ s)
printed-language r = r , parse-print r , ≈-refl
