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

data Id {A : Type} : A → A → Type where
 refl : (a : A) → Id a a

pathInd : {A : Type} (P : {x y : A} → (Id x y) → Type) →
        (∀ x → P (refl x)) → ∀ {x y} (p : (Id x y)) → P p
pathInd P r (refl x) = r _

indisc : {A : Type} (P : A → Type) {x y : A} →
       (Id x y) → P x → P y
indisc P = pathInd (λ {u v} _ → P u → P v) (λ x p → p)

-- Lemma 2.2.1. Functions behave functorially on paths:
-- Given a function f : A → B and objects a, b there is
-- ap ('application' or 'acting functorial[on paths]')

ap : {A B : Type} (f : (A → B)) {a a' : A} → 
   Id a a' → Id (f a) (f a')
ap f = pathInd (λ {x y} _ → Id (f x) (f y)) (λ x →
       refl (f x))

-- Lemma 2.1.2. Transitivity of Equality | Concatenation of paths
-- For a type A and such objects x,y,z there is a function
-- f : (Id x y) → (Id y z) → (Id x z) sending (refl x) to itself

--trans : {A : Type} {x y z : A} → Id x y → Id y z → Id x z 
--trans = pathInd (λ {x y z} _ → {z}) (λ x → D x z)

D : (A : Type) → (x y : A) → Id x y → (z : A) → Id y z → Id x z
D A x y _ = pathInd (λ A x y _ (z : A) → Id y z → Id x z)
          (λ x → (z : A) → id (Id x z))