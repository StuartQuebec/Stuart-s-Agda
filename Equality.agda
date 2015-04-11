{-# OPTIONS --without-K #-}

open import BasicTypes

module Equality where

infix 4 _==_

data _==_ {ℓ} {A : Type ℓ} (a : A) : A → Type ℓ where
 refl : a == a

pathInd : ∀ {m n} {A : Set m} → 
          (C : {x y : A} → {p : x == y} → Set n) →
          ((x : A) → C {x} {x} {refl}) →
          {x y : A} (p : x == y) → C {x} {y} {p}
pathInd C c {x} refl = c x

-- todo : Proof that idEq is actually the identity
idEq : {A : Set} {x y : A} → x == y → x == y
idEq = pathInd (_ == _) (λ x → refl)

sym : ∀ {m} {A : Type m} {x y : A} → x == y → y == x
sym = pathInd (_ == _) (λ x → refl)

trans : forall {m} {A : Type m} {x y z : A} → x == y → y == z → x == z
trans = pathInd (_ == _ → _ == _) (λ x → id)

_◾_ : forall {m} {A : Type m} {x y z : A} → x == y → y == z → x == z
p ◾ q = trans p q

nPath : (A : Type₀) (x y : A) → (p : x == y) → (p ◾ refl) == p
nPath A x y = pathInd (λ {x} {y} {p : x == y} → (p ◾ refl) == p) (λ a → refl)

