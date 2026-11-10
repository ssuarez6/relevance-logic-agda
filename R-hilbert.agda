module R-hilbert where

open import Data.String using (String)
open import Data.List using (List; length; lookup; _++_; []; [_]; _∷_)
open import Data.Fin using (Fin; zero; suc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Product using (∃; _,_)
open import Relation.Binary.PropositionalEquality using (refl; _≡_)

data Form : Set where
  Var : String → Form
  _⇒_ : Form → Form → Form

variable
  X Y Z : Form
  A B C : Form

Ctx : Set
Ctx = List Form

variable
  Γ : Ctx

data Axiom : Form → Set where
  identity         : Axiom (X ⇒ X)
  suffixing        : Axiom ((X ⇒ Y) ⇒ ((Y ⇒ Z) ⇒ (X ⇒ Z)))
  permutation      : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ (Y ⇒ (X ⇒ Z)))
  self-dist        : Axiom ((X ⇒ (Y ⇒ Z)) ⇒ ((X ⇒ Y) ⇒ (X ⇒ Z)))

infix 4 _⊩_ _⊢_
infixr 6 _⇒_

-- def. 1
data _⊩_ (Γ : Ctx) : (A : Form) → Set where
  ax  : Axiom A → Γ ⊩ A                              -- axiom
  hyp : (i : Fin (length Γ)) → (Γ ⊩ lookup Γ i)      -- element of Γ
  mp  : Γ ⊩ (A ⇒ B) → Γ ⊩ A → Γ ⊩ B                  -- modus ponens

private
  p q : Form
  p = Var "p"
  q = Var "q"

dx : [] ⊩ (p ⇒ p)
dx = ax identity

d1 : (p ⇒ q) ∷ [ p ] ⊩ q
d1 = mp (hyp zero) (hyp (suc zero))
--d1 = mp (hyp (suc zero)) (hyp zero)

d2 : p ∷ [ p ⇒ q ] ⊩ q
d2 = mp (hyp (suc zero)) (hyp zero) 
--d2 = mp (hyp zero) (hyp (suc zero))

-- unused hyp.
d3 : q ∷ p ∷ [ p ⇒ q ] ⊩ q
d3 = mp (hyp (suc (suc zero))) (hyp (suc zero))

d31 : q ∷ p ∷ [ p ⇒ q ] ⊩ q
d31 = hyp zero

d4 : p ∷ p ∷ [ p ⇒ q ] ⊩ q
d4 = mp (hyp (suc (suc zero))) (hyp zero)
--d4 = mp (hyp (suc (suc zero))) (hyp (suc zero))

weak : p ∷ [ q ] ⊩ p   -- !!!
weak = hyp zero

-- verifying used hypotheses
used : Γ ⊩ A → List (Fin (length Γ))
used (ax _)   = []
used (hyp i)  = [ i ]
used (mp d e) = used d ++ used e

-- def. 4/5
-- there is a relevant deduction d of A from Γ
-- if for every i in Γ, i is in `used d`
record _⊢_ (Γ : Ctx) (A : Form) : Set where
  field
    deduction : Γ ⊩ A
    all-used  : (i : Fin (length Γ)) → i ∈ (used deduction)

Γ₁ : Ctx
Γ₁ = (p ⇒ q) ∷ [ p ]


da : Γ₁ ⊩ q
da = mp (hyp zero) (hyp (suc zero))

db : Γ₁ ⊩ q
db = mp (mp (ax identity) (hyp zero)) (hyp (suc zero))

ea : Γ₁ ⊢ q
ea = record { deduction = da
            ; all-used  = λ { zero       → here refl
                            ; (suc zero) → there (here refl) } }

eb : Γ₁ ⊢ q
eb = record { deduction = db
            ; all-used  = λ { zero       → here refl
                            ; (suc zero) → there (here refl) } }

Γ₂ : Ctx
Γ₂ = p ∷ [ q ]

dc : Γ₂ ⊩ q
dc = hyp (suc zero)

bad : Γ₂ ⊢ q
-- bad = record { deduction = dc
--             ; all-used  = λ { zero       → here refl
--                             ; (suc zero) → here refl } }
