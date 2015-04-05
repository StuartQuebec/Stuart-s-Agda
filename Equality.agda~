{-# OPTIONS --without-K #-}

open import BasicTypes

module Equality where

infix 4 _==_

data _==_ {ℓ} {A : Type ℓ} : A → A → Type ℓ where
 refl : (a : A) → a == a

pathInd : ∀ {m n} {A : Type m} (P : {x y : A} → (x == y) → Type n) →
        (∀ x → P (refl x)) → ∀ {x y} (p : (x == y)) → P p
pathInd P r (refl x) = r _

indisc : ∀ {m n} {A : Type m} (P : A → Type n) {x y : A} →
       (x == y) → P x → P y
indisc P = pathInd (λ {u v} _ → P u → P v) (λ x p → p)

ap : ∀ {m n} {A : Type m} {B : Type n} (f : (A → B)) {a a' : A} → 
   a == a' → (f a) == (f a')
ap f = pathInd (λ {x y} _ → (f x) == (f y)) (λ x →
       refl (f x))