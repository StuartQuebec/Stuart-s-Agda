{-# OPTIONS --without-K #-}

open import Relation.Binary.PropositionalEquality
open import HoTT
open import BasicTypes

module Playground where

data List (A : Type) : Type where
 []   : List A
 _::_ : A → List A → List A

infixr 5 _::_

_++_ : {A : Type} → List A → List A → List A
[]        ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

infixr 5 _++_

List=Nat₁ : {A : Type} → List A → ℕ
List=Nat₁ [] = zero
List=Nat₁ (x :: xs) = suc (List=Nat₁ xs)

List=Nat₂ : {A : Type} →  ℕ → List A
List=Nat₂ zero = []
List=Nat₂ (suc n) = (List=Nat₂ n) ++ []

-- List and Nat are isomorphic

p : List=Nat₁ inverseOf List=Nat₂
p = ?
