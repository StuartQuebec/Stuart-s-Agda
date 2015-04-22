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

ap : ∀ {m n} {A : Type m} {B : Type n} → (f : A → B) →
     (x y : A) → (x == y) → ((f x) == (f y))
ap f x y = pathInd (λ {x} {y} {p} → ((f x) == (f y))) (λ a → refl)

sym : ∀ {m} {A : Type m} {x y : A} → x == y → y == x
sym = pathInd (λ {x} {y} {p : x == y} → y == x) (λ a → refl)

trans : forall {m} {A : Type m} {x y z : A} → x == y → y == z → x == z
trans {m} {A} {x} {y} {z} = pathInd (λ {x} {y} {p : x == y}
              → y == z → x == z) (λ x → id)

_◾_ : forall {m} {A : Type m} {x y z : A} → x == y → y == z → x == z
p ◾ q = trans p q

nPathr : ∀ {m} {A : Type m} {x y : A} → (p : x == y) → (p ◾ refl) == p
nPathr = pathInd (λ {x} {y} {p : x == y} → (p ◾ refl) == p) (λ a → refl)

nPathl : ∀ {m} {A : Type m} {x y : A} → (p : x == y) → (refl ◾ p) == p
nPathl = pathInd (λ {x} {y} {p : x == y} → (refl ◾ p) == p) (λ a → refl)

! : ∀ {i} {A : Set i} {x y : A} → (x == y → y == x)
! refl = refl

$2,14ii : ∀ {m} {A : Type m} {x y : A} (p : x == y) → (p ◾ (! p)) == refl
$2,14ii = pathInd (λ {x} {y} {p : x == y} → (p ◾ (! p)) == refl) (λ a → refl)

$2,14iii : ∀ {m} {A : Type m} {x y : A} (p : x == y) → ! (! p) == p
$2,14iii = pathInd (λ {x} {y} {p : x == y} → ! (! p) == p) (λ x → refl)

-- Associativity of Equality

help : ∀ {m} {A : Type m} {w x y z : A} → (q : x == y) →
      (r : y == z) → refl ◾ (q ◾ r) == (refl ◾ q) ◾ r

help {m} {A} {w} {x} {y} {z} q r = nPathl (q ◾ r) ◾ 
                 ap (λ (pf : x == y) → pf ◾ r) q (refl ◾ q) (nPathl q) 


ass : ∀ {m} {A : Type m} {w x y z : A} → (p : w == x) → (q : x == y) →
      (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r
ass {m} {A} {w} {x} {y} {z} = pathInd (λ {w} {x} {p : w == x} →
        (q : x == y) → (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r)
        (λ x' (q : x' == y) (r : y == z) 
        → help {m} {A} {w} {x} {y} {z} q r)