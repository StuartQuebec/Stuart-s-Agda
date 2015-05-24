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

data ℕ : Set where
 zero : ℕ
 suc : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

Type : (n : Level) → Set (lsuc n)
Type n = Set n


Type₀ = Set0
Type₁ = Set1


Typ = Type₀
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

_°_ : ∀ {l m n} {A : Type l} {B : Type m} {C : Type n} →
        (g : B → C) → (f : A → B) → A → C
g ° f = λ a → g (f a)

const : ∀ {m n} {A : Type m} {B : Type n} → B → (A → B)
const x = λ _ → x

id : ∀ {ℓ} {A : Type ℓ} → A → A
id {A} = (λ x → x)

flipDouble : ∀ {m n o p} {A : Type m} {B : Type n} {C : Type o} {D : Type p} →
       (f : A → B → C → D) → B → C → A → D
flipDouble f b c a = f a b c

asdf : ∀ {l m n} {A : Type l} {B : Type m} {C : Type n} →
        (f : A → B) → A → (g : B → C) → C
asdf = flipDouble _°_

----------------------------------
-----(Dependent) Pair Types---------
----------------------------------

-- todo : recursor

data ∑ {m n} (A : Type m) (B : (A → Type n)) : Type (m ⊔ n) where
 _,_  : (a : A) → B a → ∑ A B

--rec∑ : ∀ {m n o} {A : Type m} {B : (A → Type n)} {C : Type o} → 
--         (f : (a : A) → B a) → (∑ A B) → C
--rec∑ f (a , b) = (f a) b

proj₁ : ∀ {m} {A : Type m} {n} {B : (A → Type n)} → ∑ A B → A
proj₁ (a , b) = a

proj₂ : ∀ {m} {A : Type m} {n} {B : (A → Type n)} →
      (x : ∑ A B) → B (proj₁ x)
proj₂ (a , b) = b 


-- Simple Pair Type

_×_ : ∀ {m n} (A : Type m) (B : Type n) → Type (m ⊔ n)
A × B = ∑ A (λ _ → B)

rec× : ∀ {m n o} {A : Type m} {B : Type n} {C : Type o} →
       (f : A → B → C) → ((A × B) → C)
rec× f (a , b) = f a b

ind× : ∀ {m n} {A : Type m} {B : Type n} {C : A × B → Type (m ⊔ n)} →
       (f : (a : A) → (b : B) → C (a , b)) → ((x : A × B) → (C x))
ind× f (a , b) = f a b

----------------------------------
------- Natural Numbers ----------
----------------------------------


constℕ : ∀ {m} {A : Type m} → A → Type₀
constℕ = (const ℕ)

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


