{-# OPTIONS --safe --without-K #-}

module Rumus.Parser.Properties where

open import Data.Bool.Base using (true; false)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List.Base using ([]; _∷_)
open import Data.Nat.Base using (suc)
open import Data.Product.Base using (_,_)
open import Data.String.Base using (String; toList)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality.Core using (_≡_; refl; subst; trans; sym)
open import Rumus.Regex
open import Rumus.Parser
open import Rumus.Parser.Token
import Rumus.Parser.Grammar as G

impossible : ∀ {X Y : Set} {x : X} {y : Y} → (inj₁ x ≡ inj₂ y) → ⊥
impossible ()

right-injective : ∀ {X Y : Set} {x y : Y} → (_≡_ {A = X ⊎ Y} (inj₂ x) (inj₂ y)) → x ≡ y
right-injective refl = refl

sequence-sound : ∀ ops rs os ss → push-sequence ops rs ≡ inj₂ (os , ss) → G.Sequence ops rs os ss
sequence-sound [] rs .(sequence ∷ []) .rs refl = G.empty
sequence-sound (group ∷ ops) rs .(sequence ∷ group ∷ ops) .rs refl = G.group
sequence-sound (choice ∷ ops) rs .(sequence ∷ choice ∷ ops) .rs refl = G.choice
sequence-sound (sequence ∷ ops) [] os ss ()
sequence-sound (sequence ∷ ops) (r ∷ []) os ss ()
sequence-sound (sequence ∷ ops) (s ∷ r ∷ rs) os ss h = G.reduce (sequence-sound ops ((r ∙ s) ∷ rs) os ss h)

sequence-complete : ∀ {ops rs os ss} → G.Sequence ops rs os ss → push-sequence ops rs ≡ inj₂ (os , ss)
sequence-complete G.empty = refl
sequence-complete G.group = refl
sequence-complete G.choice = refl
sequence-complete (G.reduce h) = sequence-complete h

choice-sound : ∀ ops rs os ss → push-choice ops rs ≡ inj₂ (os , ss) → G.Choice ops rs os ss
choice-sound [] rs .(choice ∷ []) .rs refl = G.empty
choice-sound (group ∷ ops) rs .(choice ∷ group ∷ ops) .rs refl = G.group
choice-sound (choice ∷ ops) [] os ss ()
choice-sound (choice ∷ ops) (r ∷ []) os ss ()
choice-sound (choice ∷ ops) (s ∷ r ∷ rs) os ss h = G.union (choice-sound ops ((r ∪ s) ∷ rs) os ss h)
choice-sound (sequence ∷ ops) [] os ss ()
choice-sound (sequence ∷ ops) (r ∷ []) os ss ()
choice-sound (sequence ∷ ops) (s ∷ r ∷ rs) os ss h = G.concat (choice-sound ops ((r ∙ s) ∷ rs) os ss h)

choice-complete : ∀ {ops rs os ss} → G.Choice ops rs os ss → push-choice ops rs ≡ inj₂ (os , ss)
choice-complete G.empty = refl
choice-complete G.group = refl
choice-complete (G.union h) = choice-complete h
choice-complete (G.concat h) = choice-complete h

close-sound : ∀ ops rs os ss → close ops rs ≡ inj₂ (os , ss) → G.Close ops rs os ss
close-sound [] rs os ss ()
close-sound (group ∷ ops) rs .ops .rs refl = G.group
close-sound (choice ∷ ops) [] os ss ()
close-sound (choice ∷ ops) (r ∷ []) os ss ()
close-sound (choice ∷ ops) (s ∷ r ∷ rs) os ss h = G.union (close-sound ops ((r ∪ s) ∷ rs) os ss h)
close-sound (sequence ∷ ops) [] os ss ()
close-sound (sequence ∷ ops) (r ∷ []) os ss ()
close-sound (sequence ∷ ops) (s ∷ r ∷ rs) os ss h = G.concat (close-sound ops ((r ∙ s) ∷ rs) os ss h)

close-complete : ∀ {ops rs os ss} → G.Close ops rs os ss → close ops rs ≡ inj₂ (os , ss)
close-complete G.group = refl
close-complete (G.union h) = close-complete h
close-complete (G.concat h) = close-complete h

finish-sound : ∀ ops rs r → finish ops rs ≡ inj₂ r → G.Finish ops rs r
finish-sound [] [] r ()
finish-sound [] (r ∷ []) .r refl = G.done
finish-sound [] (r ∷ s ∷ rs) result ()
finish-sound (group ∷ ops) rs r ()
finish-sound (choice ∷ ops) [] r ()
finish-sound (choice ∷ ops) (r ∷ []) result ()
finish-sound (choice ∷ ops) (s ∷ r ∷ rs) result h = G.union (finish-sound ops ((r ∪ s) ∷ rs) result h)
finish-sound (sequence ∷ ops) [] r ()
finish-sound (sequence ∷ ops) (r ∷ []) result ()
finish-sound (sequence ∷ ops) (s ∷ r ∷ rs) result h = G.concat (finish-sound ops ((r ∙ s) ∷ rs) result h)

finish-complete : ∀ {ops rs r} → G.Finish ops rs r → finish ops rs ≡ inj₂ r
finish-complete G.done = refl
finish-complete (G.union h) = finish-complete h
finish-complete (G.concat h) = finish-complete h

prepare-sound : ∀ expect ops rs os ss → prepare expect ops rs ≡ inj₂ (os , ss) → G.Prepared expect ops rs os ss
prepare-sound true ops rs .ops .rs refl = G.first
prepare-sound false ops rs os ss h = G.next (sequence-sound ops rs os ss h)

prepare-complete : ∀ {expect ops rs os ss} → G.Prepared expect ops rs os ss → prepare expect ops rs ≡ inj₂ (os , ss)
prepare-complete G.first = refl
prepare-complete (G.next h) = sequence-complete h

loop-sound : ∀ cs n expect ops rs r → parse-loop cs n expect ops rs ≡ inj₂ r → G.Grammar cs expect ops rs r
loop-sound [] n true ops rs r ()
loop-sound [] n false ops rs r h with finish ops rs in ef
... | inj₁ e = ⊥-elim (impossible h)
... | inj₂ s = subst (G.Grammar [] false ops rs) (right-injective h) (G.done (finish-sound ops rs s ef))
loop-sound (c ∷ cs) n expect ops rs r h with kind c in ek | expect
... | opening | need with prepare need ops rs in ep
...   | inj₁ e = ⊥-elim (impossible h)
...   | inj₂ (os , ss) = G.opening ek (prepare-sound need ops rs os ss ep)
  (loop-sound cs (suc n) true (group ∷ os) ss r h)
loop-sound (c ∷ cs) n expect ops rs r h | closing | true = ⊥-elim (impossible h)
loop-sound (c ∷ cs) n expect ops rs r h | closing | false with close ops rs in ep
... | inj₁ e = ⊥-elim (impossible h)
... | inj₂ (os , ss) = G.closing ek (close-sound ops rs os ss ep) (loop-sound cs (suc n) false os ss r h)
loop-sound (c ∷ cs) n expect ops rs r h | alternation | true = ⊥-elim (impossible h)
loop-sound (c ∷ cs) n expect ops rs r h | alternation | false with push-choice ops rs in ep
... | inj₁ e = ⊥-elim (impossible h)
... | inj₂ (os , ss) = G.union ek (choice-sound ops rs os ss ep) (loop-sound cs (suc n) true os ss r h)
loop-sound (c ∷ cs) n expect ops rs r h | repetition | true = ⊥-elim (impossible h)
loop-sound (c ∷ cs) n expect ops [] r h | repetition | false = ⊥-elim (impossible h)
loop-sound (c ∷ cs) n expect ops (q ∷ rs) r h | repetition | false = G.star ek (loop-sound cs (suc n) false ops (star q ∷ rs) r h)
loop-sound (c ∷ []) n expect ops rs r h | escaping | need = ⊥-elim (impossible h)
loop-sound (c ∷ d ∷ cs) n expect ops rs r h | escaping | need with prepare need ops rs in ep
... | inj₁ e = ⊥-elim (impossible h)
... | inj₂ (os , ss) = G.escape ek (prepare-sound need ops rs os ss ep)
  (loop-sound cs (suc (suc n)) false os (lit d ∷ ss) r h)
loop-sound (c ∷ cs) n expect ops rs r h | ordinary | need with prepare need ops rs in ep
... | inj₁ e = ⊥-elim (impossible h)
... | inj₂ (os , ss) = G.symbol ek (prepare-sound need ops rs os ss ep)
  (loop-sound cs (suc n) false os (atom c ∷ ss) r h)

loop-complete : ∀ {cs expect ops rs r} → G.Grammar cs expect ops rs r → ∀ n → parse-loop cs n expect ops rs ≡ inj₂ r
loop-complete (G.done h) n rewrite finish-complete h = refl
loop-complete (G.opening ek G.first h) n rewrite ek = loop-complete h (suc n)
loop-complete (G.opening ek (G.next prep) h) n rewrite ek | sequence-complete prep = loop-complete h (suc n)
loop-complete (G.closing ek pop h) n rewrite ek | close-complete pop = loop-complete h (suc n)
loop-complete (G.union ek push h) n rewrite ek | choice-complete push = loop-complete h (suc n)
loop-complete (G.star ek h) n rewrite ek = loop-complete h (suc n)
loop-complete (G.escape ek G.first h) n rewrite ek = loop-complete h (suc (suc n))
loop-complete (G.escape ek (G.next prep) h) n rewrite ek | sequence-complete prep = loop-complete h (suc (suc n))
loop-complete (G.symbol ek G.first h) n rewrite ek = loop-complete h (suc n)
loop-complete (G.symbol ek (G.next prep) h) n rewrite ek | sequence-complete prep = loop-complete h (suc n)

parse-chars-sound : ∀ cs {r} → parse-chars cs ≡ inj₂ r → G.Parses cs r
parse-chars-sound cs {r} h = loop-sound cs 0 true [] [] r h

parse-chars-complete : ∀ cs {r} → G.Parses cs r → parse-chars cs ≡ inj₂ r
parse-chars-complete cs proof = loop-complete proof 0

parse-sound : ∀ (s : String) {r} → parse s ≡ inj₂ r → G.Parses (toList s) r
parse-sound s {r} h = loop-sound (toList s) 0 true [] [] r h

parse-complete : ∀ (s : String) {r} → G.Parses (toList s) r → parse s ≡ inj₂ r
parse-complete s proof = loop-complete proof 0

parse-refutes : ∀ (s : String) {e} → parse s ≡ inj₁ e → ∀ r → G.Parses (toList s) r → ⊥
parse-refutes s h r proof = impossible (trans (sym h) (parse-complete s proof))

grammar-unambiguous : ∀ {cs expect ops rs r s} → G.Grammar cs expect ops rs r → G.Grammar cs expect ops rs s → r ≡ s
grammar-unambiguous p q = right-injective (trans (sym (loop-complete p 0)) (loop-complete q 0))
