module R-arrow where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.Nat using (ℕ; _≡ᵇ_)
open import Data.Product using (_×_; _,_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.String using (String)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

data Form : Set where
  Var : String → Form
  _⇒_ : Form → Form → Form

infixr 6 _⇒_

variable
  X Y Z : Form

data Axiom : Form → Set where
  identity         : Axiom (X ⇒ X)
  suffixing        : Axiom ((X ⇒ Y) ⇒ ((Y ⇒ Z) ⇒ (X ⇒ Z)))
  permutation      : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ (Y ⇒ (X ⇒ Z)))
  self-dist        : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ ((X ⇒ Y) ⇒ (X ⇒ Z)))

-- Subscripting device is a set of natural numbers by its characteristic function
-- α n = true means n ∈ α
-- α n = false means n ∉ α
Subscript : Set
Subscript = ℕ → Bool

-- empty subscript, no number is a member
∅ : Subscript
∅ = λ _ → false

｛_｝ : ℕ → Subscript
｛ k ｝ = λ n → n ≡ᵇ k

-- n ∈ α ∪ β when n ∈ α ∨ n ∈ β 
_∪_ : Subscript → Subscript → Subscript
α ∪ β = λ n → α n ∨ β n

infixr 6 _∪_

-- hypotheses: each formula tagged with its numeral k, i.e. A{k}
Ctx : Set
Ctx = List (Form × ℕ)

variable
  A B : Form
  Γ : Ctx
  α β : Subscript
  k : ℕ

-- deduction with the subscripting device: Γ ⊢ A ^ α means A_α
data _⊢_^_ : Ctx → Form → Subscript → Set where
  ax  : Axiom A → Γ ⊢ A ^ ∅                                  -- axioms depend on nothing
  hyp : (A , k) ∈ Γ → Γ ⊢ A ^ ｛ k ｝                         -- A{k}
  mp  : Γ ⊢ (A ⇒ B) ^ α → Γ ⊢ A ^ β → Γ ⊢ B ^ (α ∪ β)        -- (A → B)α, Aβ ⊢ Bα∪β

infix 3 _⊢_^_

p q r : Form
p = Var "p"
q = Var "q"
r = Var "r"

ex-ax : [] ⊢ (p ⇒ p) ^ ∅
ex-ax = ax identity

ex-hyp : (p , 0) ∷ [] ⊢ p ^ ｛ 0 ｝
ex-hyp = hyp (here refl)

Γ₁ : Ctx
Γ₁ = (p , 0) ∷ ((p ⇒ q) , 1) ∷ []

ex-mp : Γ₁ ⊢ q ^ (｛ 1 ｝ ∪ ｛ 0 ｝)
ex-mp = mp (hyp (there (here refl))) (hyp (here refl))

ex-ax-mp : ((p ⇒ q) , 0) ∷ [] ⊢ ((q ⇒ r) ⇒ (p ⇒ r)) ^ (∅ ∪ ｛ 0 ｝)
ex-ax-mp = mp (ax suffixing) (hyp (here refl))

ex-twice : ((p ⇒ (p ⇒ q)) , 1) ∷ (p , 0) ∷ [] ⊢ q ^ ((｛ 1 ｝ ∪ ｛ 0 ｝) ∪ ｛ 0 ｝)
ex-twice = mp (mp (hyp (here refl)) (hyp (there (here refl)))) (hyp (there (here refl)))

Γ₂ : Ctx
Γ₂ = (p , 0) ∷ (p , 1) ∷ []

ex-first : Γ₂ ⊢ p ^ ｛ 0 ｝
ex-first = hyp (here refl)

ex-second : Γ₂ ⊢ p ^ ｛ 1 ｝
ex-second = hyp (there (here refl))

ex-unused : (p , 0) ∷ (q , 1) ∷ [] ⊢ p ^ ｛ 0 ｝
ex-unused = hyp (here refl)

------------------------------------------------------------------------
-- Subscripting device as a list of naturals
------------------------------------------------------------------------

Subscriptˡ : Set
Subscriptˡ = List ℕ

∅ˡ : Subscriptˡ
∅ˡ = []

｛_｝ˡ : ℕ → Subscriptˡ
｛ k ｝ˡ = k ∷ []

_∪ˡ_ : Subscriptˡ → Subscriptˡ → Subscriptˡ
αˡ ∪ˡ βˡ = αˡ ++ βˡ

infixr 6 _∪ˡ_

variable
  αˡ βˡ : Subscriptˡ

data _⊢ˡ_^_ : Ctx → Form → Subscriptˡ → Set where
  axˡ  : Axiom A → Γ ⊢ˡ A ^ ∅ˡ
  hypˡ : (A , k) ∈ Γ → Γ ⊢ˡ A ^ ｛ k ｝ˡ
  mpˡ  : Γ ⊢ˡ (A ⇒ B) ^ αˡ → Γ ⊢ˡ A ^ βˡ → Γ ⊢ˡ B ^ (αˡ ∪ˡ βˡ)

infix 3 _⊢ˡ_^_

ex-mpˡ : Γ₁ ⊢ˡ q ^ (｛ 1 ｝ˡ ∪ˡ ｛ 0 ｝ˡ)
ex-mpˡ = {!!}

ex-twiceˡ : ((p ⇒ (p ⇒ q)) , 1) ∷ (p , 0) ∷ [] ⊢ˡ q ^ ((｛ 1 ｝ˡ ∪ˡ ｛ 0 ｝ˡ) ∪ˡ ｛ 0 ｝ˡ)
ex-twiceˡ = {!!}
