{-# OPTIONS --without-K #-}

module BasicTypes where

Type : Set₁
Type = Set

data Maybe (A : Type) : Type where
 just : (a : A) →  Maybe A
 nothing : Maybe A

data Bool : Type where
 true : Bool
 false : Bool

----------------------------------
--------Functions-----------------
----------------------------------

-- Probably more useful with Universe Polymorphism!!!

const : (A B : Type) → B → (A → B)
const A B b = (λ _ → b)

----------------------------------
-----(Dependent) Pair Types---------
----------------------------------

-- todo : recursor

data ∑ (A : Type) (B : (A → Type)) : Type where
 _,_ : (a : A) → B a → ∑ A B

proj₁ : {A : Type} {B : (A → Type)} → ∑ A B → A
proj₁ (a , b) = a

proj₂ : {A : Type} {B : (A → Type)} →
      (x : ∑ A B) → B (proj₁ x)

proj₂ (a , b) = b 

-- Simple Pair Type

_×_ : (A B : Type) → Type
A × B = ∑ A (λ _ → B)

----------------------------------
------- Natural Numbers ----------
----------------------------------

data ℕ : Type where
 zero : ℕ
 suc : ℕ → ℕ

-- Predecessor

pred : ℕ → Maybe ℕ
pred zero = nothing
pred (suc n) = just n

-- Addition

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

-- Multiplication

_*_ : ℕ → ℕ → ℕ
zero * n = zero
suc m * n = m + (m * n)