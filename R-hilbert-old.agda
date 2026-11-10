module R-hilbert-old where

open import Data.String using (String)

data Form : Set where
  Var : String → Form
  _⇒_ : Form → Form → Form

infixr 6 _⇒_

variable
  A B C : Form
  X Y Z : Form

data Axiom : Form → Set where
  identity         : Axiom (X ⇒ X)
  suffixing        : Axiom ((X ⇒ Y) ⇒ ((Y ⇒ Z) ⇒ (X ⇒ Z)))
  permutation      : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ (Y ⇒ (X ⇒ Z)))
  self-dist        : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ ((X ⇒ Y) ⇒ (X ⇒ Z)))

-- entail via axiom or modus ponens
data ⊢_ : Form → Set where
  ax : Axiom A → ⊢ A
  mp : ⊢ (A ⇒ B) → ⊢ A → ⊢ B

-- A → A 
_ : ⊢ (Var "p" ⇒ Var "p")
_ = ax identity

-- transitivity
trans : ⊢ (A ⇒ B) → ⊢ (B ⇒ C) → ⊢ (A ⇒ C)
trans {A} {B} {C} ab bc = mp (mp (ax suffixing) ab) bc
--trans {A} {B} {C} = ax suffixing

-- "Weak implicational calculus"
data Axiom2 : Form → Set where
  identity    : Axiom2 (X ⇒ X)
  prefixing   : Axiom2 ((X ⇒ Y) ⇒ ((Z ⇒ X) ⇒ (Z ⇒ Y)))
  permutation : Axiom2 ((X ⇒ (Y ⇒ Z)) ⇒ (Y ⇒ (X ⇒ Z)))
  contraction : Axiom2 ((X ⇒ (X ⇒ Y)) ⇒ (X ⇒ Y))

data ⊢2_ : Form → Set where
  ax2 : Axiom2 A → ⊢2 A
  mp2 : ⊢2 (A ⇒ B) → ⊢2 A → ⊢2 B

-- transitivity in weak implicational calculus
trans2 : ⊢2 (A ⇒ B) → ⊢2 (B ⇒ C) → ⊢2 (A ⇒ C)
trans2 {A} {B} {C} ab bc = mp2 (mp2 (ax2 prefixing) bc) ab


-- ⊢ and ⊢2 are equivalent

-- the two axioms each system is missing, derived as theorems of the other
suffixing2 : ⊢2 ((X ⇒ Y) ⇒ ((Y ⇒ Z) ⇒ (X ⇒ Z)))
suffixing2 = mp2 (ax2 permutation) (ax2 prefixing)

self-dist2 : ⊢2 ((X ⇒ (Y ⇒ Z)) ⇒ ((X ⇒ Y) ⇒ (X ⇒ Z)))
self-dist2 =
  mp2 (mp2 (ax2 prefixing) (mp2 (ax2 prefixing) (ax2 contraction)))
      (mp2 (mp2 (ax2 prefixing) (ax2 permutation)) (mp2 (ax2 prefixing) (ax2 prefixing)))

prefixing1 : ⊢ ((X ⇒ Y) ⇒ ((Z ⇒ X) ⇒ (Z ⇒ Y)))
prefixing1 = mp (ax permutation) (ax suffixing)

contraction1 : ⊢ ((X ⇒ (X ⇒ Y)) ⇒ (X ⇒ Y))
contraction1 = mp (mp (ax permutation) (ax self-dist)) (ax identity)

to2 : ⊢ A → ⊢2 A
to2 (ax identity)    = ax2 identity
to2 (ax suffixing)   = suffixing2
to2 (ax permutation) = ax2 permutation
to2 (ax self-dist)   = self-dist2
to2 (mp f a)         = mp2 (to2 f) (to2 a)

from2 : ⊢2 A → ⊢ A
from2 (ax2 identity)    = ax identity
from2 (ax2 prefixing)   = prefixing1
from2 (ax2 permutation) = ax permutation
from2 (ax2 contraction) = contraction1
from2 (mp2 f a)         = mp (from2 f) (from2 a)


-- entailment from a context of premises
open import Data.List using (List; []; _∷_; _++_; [_]; reverse)

Ctx : Set
Ctx = List Form

variable
  Γ Δ : Ctx

open import Data.Fin using (Fin; zero; suc)
open import Data.List using (length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Any.Properties using (++⁺ˡ; ++⁺ʳ)
open import Data.Product using (∃; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Data.List using (lookup)

infix 4 _⊩_∣_ _⊢_

-- un solo contexto Γ fijo en toda la derivación
data _⊩_∣_ (Γ : Ctx) : Form → List (Fin (length Γ)) → Set where
  ax  : Axiom A → Γ ⊩ A ∣ []
  hyp : (i : Fin (length Γ)) → Γ ⊩ lookup Γ i ∣ [ i ]
  mp  : ∀ {U V} → Γ ⊩ (A ⇒ B) ∣ U → Γ ⊩ A ∣ V → Γ ⊩ B ∣ (U ++ V)

-- relevante: toda premisa de Γ se usa al menos una vez
_⊢_ : Ctx → Form → Set
Γ ⊢ A = ∃ λ U → Γ ⊩ A ∣ U × (∀ i → i ∈ U)

-- examples
private
  p q r : Form
  p = Var "p"
  q = Var "q"
  r = Var "r"

-- p ⊢ p
ex1 : [ p ] ⊢ p
ex1 = _ , hyp zero , λ { zero → here refl }

-- ⊢ p ⇒ p, no premises
ex2 : [] ⊢ p ⇒ p
ex2 = _ , ax identity , λ ()

-- exex : (p ⇒ q) ∷ [ p ] ⊢ p   -- no es derivable: p ⇒ q quedaría sin usar

-- p ⇒ q, p ⊢ q  (modus ponens from premises)
ex3 : (p ⇒ q) ∷ [ p ] ⊢ q
ex3 = _ , mp (hyp zero) (hyp (suc zero))
        , λ { zero → here refl ; (suc zero) → there (here refl) }

-- p ⇒ q, q ⇒ r ⊢ p ⇒ r
ex4 : (p ⇒ q) ∷ [ q ⇒ r ] ⊢ (p ⇒ r)
ex4 = _ , mp (mp (ax suffixing) (hyp zero)) (hyp (suc zero))
        , λ { zero → here refl ; (suc zero) → there (here refl) }

-- p ⇒ (p ⇒ q), p, p ⊢ q  (p used twice, so it appears twice)
ex5 : (p ⇒ (p ⇒ q)) ∷ p ∷ [ p ] ⊢ q
ex5 = _ , mp (mp (hyp zero) (hyp (suc zero))) (hyp (suc (suc zero)))
        , λ { zero → here refl ; (suc zero) → there (here refl)
            ; (suc (suc zero)) → there (there (here refl)) }

-- p ⊬ q : no weakening, so an unused premise is rejected
-- ex6 : p ∷ [ q ] ⊢ q
