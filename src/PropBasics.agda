module PropBasics where

-- Propositions are just types or "Set"s
Prp : Set₁
Prp = Set

-- This syntax just lets us to quantify over variable names in this file
-- So we don't need to introduce them everywhere
variable
    P Q R : Prp

infixl 50 ¬_
infixl 40 _∧_ _∨_
infixl 30 _⇒_
infixl 20 _⊢_ _≈_

-- Logical AND, Product, (A,B), or A × B
data _∧_ (P Q : Prp) : Prp where
  _,_ : (p : P) -> (q : Q) -> P ∧ Q

-- Logical Impliciation, or "If"
_⇒_ : (P Q : Prp) -> Prp
P ⇒ Q = P -> Q

_⊢_ : (P Q : Prp) -> Prp
_⊢_ = _⇒_

-- Logical OR, Either, or Sum types
data _∨_ (P Q : Prp) : Prp where
  inl : (p : P) -> P ∨ Q
  inr : (q : Q) -> P ∨ Q

-- Logical False, or the empty type, or Nothing
data ⊥ : Prp where

-- Logical True, or the unit type
data ⊤ : Prp where
  unit : ⊤

-- Logical NOT, or negation
-- Equivalently, ¬ P is the same as assuming P is true then showing an absurdity
¬_ : (P : Prp) -> Prp
¬ P = P ⇒ ⊥

-- If we assume something false, we can prove anything
absurd : ⊥
       ⊢ P
absurd ()

-- We can always prove true, no matter what we assume
always : P
       ⊢ ⊤
always p = unit

-- Let's prove some other theorems about propositions
-- Or alternatively "let's write some programs with types"
modus-ponens : (P ⇒ Q)
             ∧ P
             ⊢ Q
modus-ponens (p , q) = p q

∧-comm : P ∧ Q
       ⊢ Q ∧ P
∧-comm (p , q) = q , p

∨-assoc : ((P ∨ Q) ∨ R)
        ⊢ (P ∨ (Q ∨ R))
∨-assoc (inl (inl p)) = inl p
∨-assoc (inl (inr q)) = inr (inl q)
∨-assoc (inr q)       = inr (inr q)

p-notnot : P
         ⊢ ¬ ¬ P
p-notnot p q = q p

demorgans₁ : ¬ P ∧ ¬ Q
          ⊢ ¬ (P ∨ Q)
demorgans₁ (p , q) (inl r) = p r
demorgans₁ (p , q) (inr r) = q r

demorgans₂ : ¬ (P ∨ Q)
           ⊢ ¬ P ∧ ¬ Q
demorgans₂ p = (λ q → p (inl q)) , λ q → p (inr q)

-- Mutual Implication, or IFF, or "If and only if"
_≈_ : Prp -> Prp -> Prp
P ≈ Q = (P ⇒ Q) ∧ (Q ⇒ P)

demorgans : ¬ (P ∨ Q) ≈ ¬ P ∧ ¬ Q
demorgans = demorgans₂ , demorgans₁

open import Function

-- Some shockingly easy theorems to prove using elementary functions like app, and composition
contrapositive :   P ⇒   Q
               ⊢ ¬ Q ⇒ ¬ P
contrapositive p q = q ∘ p

i-dont-know : ¬ (P ∧ ¬ P)
i-dont-know (p , q) = q p

----------------------------------------------
-- And now for something completely unrelated
----------------------------------------------

data TLang : Set where
  bool : TLang
  num  : TLang

data Lang : TLang -> Set where
  true : Lang bool
  false : Lang bool
  zero : Lang num
  succ : Lang num -> Lang num
  add : Lang num -> Lang num -> Lang num
  ifthenelse : {t : TLang} -> Lang bool -> Lang t -> Lang t -> Lang t

exp : Lang num
exp = add (add (succ zero) (succ (succ zero))) (succ (succ (succ zero)))

exp2 : Lang bool
exp2 = ifthenelse true true false


open import Data.Bool
open import Data.Nat

evalT : TLang -> Set
evalT bool = Bool
evalT num = ℕ

eval : {t : TLang} -> Lang t -> evalT t
eval true = true
eval false = false
eval zero = 0
eval (succ e) = 1 + (eval e)
eval (add e f) = eval e + eval f
eval (ifthenelse e e₁ e₂) = if eval e then eval e₁ else eval e₂

backagain : {t : TLang} -> evalT t -> Lang t
backagain {bool} false = false
backagain {bool} true = true
backagain {num} zero = zero
backagain {num} (suc T₁) = succ (backagain T₁)












--
