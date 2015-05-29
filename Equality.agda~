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

foo : (x : ℕ × ℕ) →  ℕ
foo = rec× (λ m n → m + n)

-- todo : Proof that idEq is actually the identity
idEq : {A : Set} {x y : A} → x == y → x == y
idEq = pathInd (_ == _) (λ x → refl)

ap : ∀ {m n} {A : Type m} {B : Type n} → (f : A → B) →
     {x y : A} → (x == y) → ((f x) == (f y))
ap f = pathInd (λ {x} {y} {p} → ((f x) == (f y))) (λ a → refl)

sym : ∀ {m} {A : Type m} {x y : A} → x == y → y == x
sym = pathInd (λ {x} {y} → y == x) (λ a → refl)

trans : forall {m} {A : Type m} {x y z : A} → x == y → y == z → x == z
trans {m} {A} {x} {y} {z} = pathInd (λ {x} {y} → y == z → x == z)
                            (λ x → id)

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

ass : ∀ {m} {A : Type m} {w x y z : A} → (p : w == x) → (q : x == y) →
      (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r
ass {m} {A} {w} {x} {y} {z} = pathInd (λ {w} {x} {p : w == x} →
        (q : x == y) → (r : y == z) → p ◾ (q ◾ r) == (p ◾ q) ◾ r)
        (λ x' (q : x' == y) (r : y == z) 
        → nPathl (q ◾ r) ◾ ap (λ (pf : x' == y) → pf ◾ r) {q} {refl ◾ q} (nPathl q))

-- transport

trp : ∀ {m n} {A : Type m} {x y : A} → (P : A → Type n) → x == y →
      P x → P y
trp {m} {n} {A} {x} {y} P = pathInd (λ {x} {y} → P x → P y)
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
                            (λ a → nPathr (H a) ◾ nPathl (H a))

isEquiv : ∀ {m n} {A : Type m} {B : Type n} → (f : A → B) → Type (m ⊔ n)
isEquiv {m} {n} {A} {B} f = ∑ (B → A) (λ g → (g ° f) ~ id) × (∑ (B → A) (λ g → (f ° g) ~ id))

infixl 50 _≃_

typeEquiv : ∀ {m n} (A : Type m) (B : Type n) → Type (m ⊔ n)
typeEquiv {m} {n} A B = ∑ (A → B) (λ f → isEquiv f)
_≃_ : ∀ {m n} (A : Type m) (B : Type n) → Type (m ⊔ n)
A ≃ B = typeEquiv A B



-- Characterization of the identity type on simple pairs

idTypePairs : ∀ {m n} {A : Type m} {B : Type n} {x y : A × B} →
              (p : x == y) →
              ((proj₁ x) == (proj₁ y)) × ((proj₂ x) == (proj₂ y))
idTypePairs p = (ap proj₁ p) , (ap proj₂ p)

idTypePairs⁻¹ : ∀ {m n} {A : Type m} {B : Type n} {x y : A × B} →
                ((proj₁ x) == (proj₁ y)) × ((proj₂ x) == (proj₂ y)) →
                x == y
idTypePairs⁻¹ {m} {n} {A} {B} {a , b} {a' , b'} = rec×
                  (pathInd (λ {x} {y} → b == b' → (x , b) == (y , b'))
                  (λ a → pathInd (λ {x} {y} → (a , x) == (a , y))
                         (λ b → refl)))

uniquePairs : ∀ {m n} {A : Type m} {B : Type n} → (z : A × B) → 
              z == (proj₁ z , proj₂ z)
uniquePairs {m} {n} {A} {B} z = idTypePairs⁻¹ {m} {n} {A} {B} {z} {proj₁ z , proj₂ z} (refl , refl)

$2,6,2i : ∀ {m} {A : Type m} → isEquiv id
$2,6,2i {m} {A} = (id , λ x → refl {m} {A}) , (id , λ x → refl)

help1 : ∀ {m n} {A : Type m} {B : Type n} (x : A × B)
       → ((idTypePairs⁻¹ {m} {n} {A} {B} {x} {x}) ° (idTypePairs {m} {n} {A} {B} {x} {x}))
         refl == refl
help1 (a , b) = refl

help2' : ∀ {m n} {A : Type m} {B : Type n} (a : A) → (b : B) → (a' : A) → (b' : B) →
        (pq : (a == a') × (b == b')) →
        (((idTypePairs {m} {n} {A} {B} {a , b} {a' , b'}) ° idTypePairs⁻¹) pq == pq)

help2' {m} {n} {A} {B} a b a' b' = (ind× (pathInd (λ {a} {a'} {p} → (q : b == b') →
                                                   (((idTypePairs {m} {n} {A} {B} {a , b} {a' , b'}) ° idTypePairs⁻¹) (p , q)) == (p , q) )
                                 (λ a → (pathInd (λ {b} {b'} {q} → 
                                                 (((idTypePairs {m} {n} {A} {B} {a , b} {a , b'}) ° idTypePairs⁻¹) (refl , q)) == (refl , q))
                                                  (λ x' → refl)))))

help2 : ∀ {m n} {A : Type m} {B : Type n} → (x y : A × B) → (pq : (proj₁ x == proj₁ y) ×
         (proj₂ x == proj₂ y)) → (((idTypePairs {m} {n} {A} {B} {x} {y}) ° idTypePairs⁻¹) pq) == pq
help2  = 2ind× help2'

$2,6,2 : ∀ {m n} {A : Type m} {B : Type n} {x y : A × B} → isEquiv 
         (idTypePairs {m} {n} {A} {B} {x} {y})
$2,6,2 {m} {n} {A} {B} {x} {y} = (idTypePairs⁻¹ , pathInd (λ {x} {y} {p} → (idTypePairs⁻¹ ° idTypePairs) p == p) (λ x → help1 x )) ,
                                 (idTypePairs⁻¹ , help2 x y)

$2,6,4 : ∀ {m n} {Z : Type m} {A B : Z → Type n} {x y : Z} → (p : x == y) → (w : A x × B x) →
         (trp (λ (z : Z) → (A z) × (B z)) p w) == (trp A p (proj₁ w)) , (trp B p (proj₂ w))

$2,6,4 {m} {n} {Z} {A} {B} = pathInd (λ {x} {y} {p} → (w : A x × B x) →
           (trp (λ (z : Z) → (A z) × (B z)) p w) == (trp A p (proj₁ w)) , (trp B p (proj₂ w))) 
           (λ x w → uniquePairs w)

$2,6,5 : ∀ {k l m n} {A : Type k} {B : Type l} {A' : Type m} {B' : Type n} {f : A → A'} {g : B → B'}
          → (x y : A × B) → (p : proj₁ x  == proj₁ y) → (q : proj₂ x == proj₂ y) →
          ap (λ x → (f (proj₁ x) , g (proj₂ x))) (idTypePairs⁻¹ {k} {l} {A} {B} {x} {y} (p , q)) ==
          idTypePairs⁻¹ ((ap f p) , (ap g q))

$2,6,5 {k} {l} {m} {n} {A} {B} {A'} {B'} {f} {g} = 2ind× (λ a b a' b' →
        pathInd (λ {a} {a'} {p} → (q : b == b') → ap (λ x → (f (proj₁ x) , g (proj₂ x)))
                       (idTypePairs⁻¹ {k} {l} {A} {B} {a , b} {a' , b'} (p , q)) == idTypePairs⁻¹ ((ap f p) , (ap g q)))
                (λ a → pathInd (λ {b} {b'} {q} → ap (λ x → (f (proj₁ x) , g (proj₂ x))) 
                     (idTypePairs⁻¹ {k} {l} {A} {B} {a , b} {a , b'} (refl , q)) == idTypePairs⁻¹ ((ap f refl) , (ap g q)))
                (λ b → refl)))

-- Characterization Identity Type Dependent Pairs

idTypeDepPairs : ∀ {m n} {A : Type m} {P : A → Type n} {w w' : ∑ A P} → w == w' →
                 ∑ ((proj₁ w) == (proj₁ w')) (λ p → (trp P p (proj₂ w) == (proj₂ w')))
idTypeDepPairs {m} {n} {A} {P} {w} {w'} =  pathInd (λ {w} {w'} → ∑ ((proj₁ w) == (proj₁ w')) (λ p → (trp P p (proj₂ w) == (proj₂ w')))) 
                                  (λ w → refl , refl)  

helpp : ∀ {m n} {A : Type m} {P : A → Type n} {a : A} {b : (P a)} {a' : A} {b' : (P a)} → (p : a == a') → (b == b') → 
        (a , b) == (a' , b')
helpp = {!!}

idTypeDepPairs⁻¹ : ∀ {m n} {A : Type m} {P : A → Type n} (w w' : ∑ A P) → 
                   ∑ ((proj₁ w) == (proj₁ w')) (λ p → (trp P p (proj₂ w) == (proj₂ w'))) → w == w'
idTypeDepPairs⁻¹ {m} {n} {A} {P} = 2ind∑ (λ w₁ w₂ w₁' w₂' → {!ind∑ helpp!})
                                                                --    (w₁ , w₂) == (w₁' , w₂')) ?!})

$2,7,2 : ∀ {m n} {A : Type m} {P : A → Type n} {w w' : ∑ A P} →
         (w == w') ≃ (∑ (proj₁ w == proj₁ w') (λ p → trp P p (proj₂ w) == proj₂ w'))
$2,7,2 = idTypeDepPairs , {!!}