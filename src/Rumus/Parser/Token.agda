{-# OPTIONS --safe --without-K #-}

module Rumus.Parser.Token where

open import Data.Char.Base using (Char)

data Kind : Set where
  opening closing alternation repetition escaping ordinary : Kind

kind : Char → Kind
kind '(' = opening
kind ')' = closing
kind '|' = alternation
kind '*' = repetition
kind '\\' = escaping
kind _ = ordinary
