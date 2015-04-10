{-# OPTIONS --without-K #-}

open import BasicTypes

module Equality where

infix 4 _==_

data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
 refl : a == a

pathInd : ∀ {m n} → {A : Set m} → 
          (C : {x y : A} → x == y → Set n) →
          (c : (x : A) → C {x} refl) →
          {x y : A} (p : x == y) → C {x} p
pathInd C c {x} refl = c x

-- todo : Proof that idEq is actually the identity
idEq : {A : Set} {x y : A} → x == y → x == y
idEq {A} = pathInd (λ {x y : A} p → x == y) (λ x → refl)

foo : ∀ {m} (A : Type m) {x y : A} → (x == y) → ℕ
foo A p = zero
--foo A = pathInd (λ {x y : A} p → ℕ) (λ x → zero)

sym : ∀ {m} (A : Type m) {x y : A} → x == y → y == x
sym A = pathInd (λ {x y : A} _ → y == x) (λ x → refl)

trans : ∀ {m} (A : Type m) {x y : A} → x == y → (z : A) → y == z → x == z
trans A = pathInd (λ {x y : A} _ → (z : A) → y == z → x == z) (λ x → (λ z p → p))

--_◾_ : ∀ {m} (A : Type m) {x y z : A} → x == y → y == z → x == z
--◾_ = {!trans A!}
