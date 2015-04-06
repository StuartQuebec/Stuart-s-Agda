{-# OPTIONS --without-K #-}

open import BasicTypes
open import Relation.Binary.PropositionalEquality

module HoTT where

Endo : Type → Type
Endo A = A → A

_leftInverseOf_ : {A : Type} → Endo A → Endo A → Type
f leftInverseOf g = ∀ x → f (g x) ≡ x

_rightInverseOf_ : {A : Type} → Endo A → Endo A → Type
f rightInverseOf g = ∀ x → g (f x) ≡ x

_inverseOf_ : {A : Type} → Endo A → Endo A → Type
f inverseOf g = (f leftInverseOf g) × (f rightInverseOf g)

