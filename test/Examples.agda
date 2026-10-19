{-# OPTIONS --safe --without-K #-}

module Examples where

open import Data.Bool.Base using (Bool; true; false)
open import Data.Char.Base using (Char)
open import Data.List.Base using ([]; _∷_)
open import Data.String.Base using (toList)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Rumus
import Rumus.Match

bit-equal : DecidableEquality Bool
bit-equal true true = yes refl
bit-equal false false = yes refl
bit-equal true false = no (λ ())
bit-equal false true = no (λ ())

module Binary = Rumus.Match bit-equal

binary-alphabet : Binary.accepts (star (lit false ∪ lit true)) (false ∷ true ∷ []) ≡ true
binary-alphabet = refl

a b : Regex Char
a = lit 'a'
b = lit 'b'

suffix : Regex Char
suffix = ((star (a ∪ b) ∙ a) ∙ b) ∙ b

empty-rejects : accepts ∅ [] ≡ false
empty-rejects = refl

epsilon-accepts : accepts ε [] ≡ true
epsilon-accepts = refl

literal-rejects-empty : accepts a [] ≡ false
literal-rejects-empty = refl

suffix-accepts : accepts suffix (toList "aabb") ≡ true
suffix-accepts = refl

suffix-rejects : accepts suffix (toList "abab") ≡ false
suffix-rejects = refl

nullable-star : accepts (star (ε ∪ a)) (toList "aaa") ≡ true
nullable-star = refl

membership-proof : Dec (toList "aabb" ∈ suffix)
membership-proof = match suffix (toList "aabb")

canonical-union : normalize ((b ∪ a) ∪ (a ∪ ∅)) ≡ (a ∪ b)
canonical-union = refl

zero-product : normalize (star a ∙ ∅) ≡ ∅
zero-product = refl

epsilon-product : normalize ((ε ∙ a) ∙ ε) ≡ a
epsilon-product = refl

star-collapse : normalize (star (star (star a))) ≡ star a
star-collapse = refl

epsilon-star : normalize (star ε) ≡ (ε {Char})
epsilon-star = refl

normalization-proof : normalize suffix ≈ suffix
normalization-proof = normalize-correct suffix

equivalent-example : Result (a ∙ star a) (a ∪ (a ∙ a ∙ star a))
equivalent-example = equivalence (a ∙ star a) (a ∪ (a ∙ a ∙ star a))

counterexample-example : Result (star a ∙ b) (a ∙ star b)
counterexample-example = equivalence (star a ∙ b) (a ∙ star b)

shortest-counterexample : ShortestResult (a ∙ a ∙ a ∙ a) (a ∙ a ∙ a ∙ b)
shortest-counterexample = shortest-equivalence (a ∙ a ∙ a ∙ a) (a ∙ a ∙ a ∙ b)
