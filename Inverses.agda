{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality

module Inverses where

Type : Set₁
Type = Set

Endo : Type → Type
Endo A = A → A

_leftInverseOf_ : {A : Type} → Endo A → Endo A → Type
f leftInverseOf g = ∀ x → f (g x) ≡ x

_rightInverseOf_ : {A : Type} → Endo A → Endo A → Type
f rightInverseOf g = ∀ x → g (f x) ≡ x

