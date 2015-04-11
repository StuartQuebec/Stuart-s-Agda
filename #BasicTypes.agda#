{-# OPTIONS --without-K #-}

module BasicTypes where

infixl 6 _⊔_

-- Universe Polymorphism -------------

postulate
  Level : Set
  lzero : Level
  lsuc  : Level → Level
  _⊔_   : Level → Level → Level

{-# BUILTIN LEVEL     Level #-}
{-# BUILTIN LEVELZERO lzero #-}
{-# BUILTIN LEVELSUC  lsuc  #-}
{-# BUILTIN LEVELMAX  _⊔_   #-}

Type : (n : Level) → Set (lsuc n)
Type n = Set n

Type₀ = Set0
Type₁ = Set1

--------- Maybe Type----------------------

data Maybe {ℓ} (A : Type ℓ) : Type ℓ where
 just : (a : A) →  Maybe A
 nothing : Maybe A

-----The Types with no and two inhabitants---

data ⊥ : Type₀ where 

data Bool : Type₀ where
 true : Bool
 false : Bool

--------Negation------------

¬ : ∀ {n} (A : Type n) → Type n
¬ A = A → ⊥

----------------------------------
---Basic Functions----------------
----------------------------------

const : ∀ {m n} {A : Type m} {B : Type n} → B → (A → B)
const x = λ _ → x

id : ∀ {ℓ} {A : Type ℓ} → A → A
id {A} = (λ x → x)

----------------------------------
-----(Dependent) Pair Types---------
----------------------------------

-- todo : recursor

data ∑ {m} (A : Type m) {n} (B : (A → Type n)) : Type (m ⊔ n) where
 _,_ : (a : A) → B a → ∑ A B

proj₁ : ∀ {m} {A : Type m} {n} {B : (A → Type n)} → ∑ A B → A
proj₁ (a , b) = a

proj₂ : ∀ {m} {A : Type m} {n} {B : (A → Type n)} →
      (x : ∑ A B) → B (proj₁ x)

proj₂ (a , b) = b 

-- Simple Pair Type

_×_ : ∀ {m n} (A : Type m) (B : Type n) → Type (m ⊔ n)
A × B = ∑ A (λ _ → B)

----------------------------------
------- Natural Numbers ----------
----------------------------------

data ℕ : Type₀ where
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