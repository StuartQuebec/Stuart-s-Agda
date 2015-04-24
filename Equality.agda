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
     {x y : A} → (x == y) → ((f x) == (f y))
ap f {x} {y} = pathInd (λ {x} {y} {p} → ((f x) == (f y))) (λ a → refl)

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
                 ap (λ (pf : x == y) → pf ◾ r) {q} {(refl ◾ q)} (nPathl q) 


ass : ∀ {m} {A : Type m} {w x y z : A} → (p : w == x) → (q : x == y) →
      (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r
ass {m} {A} {w} {x} {y} {z} = pathInd (λ {w} {x} {p : w == x} →
        (q : x == y) → (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r)
        (λ x' (q : x' == y) (r : y == z) 
        → help {m} {A} {w} {x'} {y} {z} q r)

-- transport

trp : ∀ {m n} {A : Type m} {x y : A} → (P : A → Type n) → x == y →
      P x → P y
trp {m} {n} {A} {x} {y} P = pathInd (λ {x} {y} {p} → P x → P y)
                                    (λ a → id)

-- functor propety of dependent functions

apd : ∀ {m n} {A : Type m} {P : A → Type n} → (f : (x : A) → P x) →
      {x y : A} → (p : x == y) → (trp P p (f x)) == f y
apd {m} {n} {A} {P} f = pathInd (λ {x} {y} {p} → (trp P p (f x)) == f y)
                 (λ a → refl)

trpConst : ∀ {m n} {A : Type m} {B : Type n}
           {x y : A} → (p : x == y) → (b : B) → trp (const B) p b == b
trpConst {m} {n} {A} {B} {x} {y} = pathInd (λ {x} {y} {p} → 
         (b : B) → trp (const B) p b == b) (λ a _ → refl)

foo : {x y : ℕ} → (p : x == y) →
      x == zero → y == zero
foo p = trp (λ a → a == zero) p

help' : ∀ {m n} {A : Type m} {x : A} {P : A → Type n} → {u : P x} →
      u == (trp P refl u)
help' = refl

help'' : {A : Type₀} {a : A} → (a , a) == (a , a)
help'' = refl


-- lemma 2.3.2 path lifting property of type families
lift : ∀ {m n} {A : Type m} {P : A → Type n} {x y : A} → (p : x == y) →
       (u : P x) → (x , u) == (y , trp P p u)
lift {m} {n} {A} {P} {x} {y} = pathInd (λ {x} {y} {p : x == y} → (u : P x) →
                               (x , u) == (y , trp P p u)) 
                               (λ x' _ → refl )

hom : ∀ {m n} {A : Type m} {P : A → Type n} → (f g : (a : A) → P a) →
      Type (m ⊔ n)
hom {m} {n} {A} {P} f g = (x : A) → (f x) == (g x)

_~_ : ∀ {m n} {A : Type m} {P : A → Type n} → (f g : (a : A) → P a) →
      Type (m ⊔ n)
f ~ g = hom f g

homRefl : ∀ {m n} {A : Type m} {P : A → Type n} → (f : (a : A) → P a) →
          f ~ f
homRefl {m} {n} {A} f = (λ (x : A) → refl)

homSym : ∀ {m n} {A : Type m} {P : A → Type n} → (f g : (a : A) → P a) →
          f ~ g → g ~ f
homSym {m} {n} {A} {P} f g h = λ (x : A) → sym (h x)

homTrans : ∀ {m n} {A : Type m} {P : A → Type n} → (e f g : (a : A) → P a) →
          e ~ f → f ~ g → e ~ g
homTrans {m} {n} {A} {P} e f g h i = λ (x : A) → (h x) ◾ (i x)

homNatTrafo : ∀ {m n} {A : Type m} {B : Type n} (f g : A → B) → (H : f ~ g) →
              {x y : A} → (p : x == y) → (H x) ◾ (ap g p) == (ap f p) ◾ (H y)
homNatTrafo f g H = pathInd (λ {x} {y} {p : x == y} 
                            → (H x) ◾ (ap g p) == (ap f p) ◾ (H y))
                            {!!}