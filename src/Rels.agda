module Rels where

open import Data.Bool
open import Data.Nat
open import Data.List

variable
  A B      : Set
  a b      : A
  n        : ℕ
  as bs cs : List A

-- List membership
-- a ∈ as means the element a appears somewhere in as
data _∈_ : A -> List A -> Set where
  here  : ∀ {  as}           -> a ∈ (a ∷ as)
  there : ∀ {b as} -> a ∈ as -> a ∈ (b ∷ as)

-- "Sublists"
-- All the elements of the first list appear in the second at least once
data _⊆_ : List A -> List A -> Set where
  []  :                      []       ⊆ as
  _∷_ : a ∈ bs -> as ⊆ bs -> (a ∷ as) ⊆ bs

-- We can enlarge the subsuming list
⊆-wkn : as ⊆ bs -> as ⊆ (b ∷ bs)
⊆-wkn []      = []
⊆-wkn (x ∷ p) = (there x) ∷ ⊆-wkn p

-- The membership relation is reflexive ...
⊆-refl : (as : List A) -> as ⊆ as
⊆-refl [] = []
⊆-refl (x ∷ as) = here ∷ ⊆-wkn (⊆-refl as)

⊆-implies-∈ : a ∈ as -> as ⊆ bs -> a ∈ bs
⊆-implies-∈ here      (x ∷ q) = x
⊆-implies-∈ (there p) (x ∷ q) = ⊆-implies-∈ p q

-- ... transitive
⊆-trans : as ⊆ bs -> bs ⊆ cs -> as ⊆ cs
⊆-trans []       q  = []
⊆-trans (p ∷ ps) qs = ⊆-implies-∈ p qs ∷ (⊆-trans ps qs)

-- Some more lemmas
∈-respects-++ : a ∈ as -> a ∈ (as ++ bs)
∈-respects-++ here = here
∈-respects-++ (there p) = there (∈-respects-++ p)

⊆-respects-++ : as ⊆ bs -> as ⊆ (bs ++ cs)
⊆-respects-++ [] = []
⊆-respects-++ (x ∷ p) = ∈-respects-++ x ∷ ⊆-respects-++ p

-- The antisymmetry of the sublist relation leads to an equivalence
data _≈_ : List A -> List A -> Set where
  eq : ∀ {as bs : List A} -> as ⊆ bs -> bs ⊆ as -> as ≈ bs

-- ... which means it's reflexive, symmetric, and transitive too
≈-refl : (as : List A) -> as ≈ as
≈-refl as = eq (⊆-refl as) (⊆-refl as)

≈-sym : as ≈ bs -> bs ≈ as
≈-sym (eq l r) = eq r l

≈-trans : as ≈ bs -> bs ≈ cs -> as ≈ cs
≈-trans (eq p q) (eq r s) = eq (⊆-trans p r) (⊆-trans s q)

-- Prefix
-- The first list is a prefix of the second
data _⊑_ : List A -> List A -> Set where
  []  : [] ⊑ as
  _∷_ : (a : A) -> as ⊑ bs -> (a ∷ as) ⊑ (a ∷ bs)

-- prefixes are a type of sublist
⊑-implies-⊆ : as ⊑ bs -> as ⊆ bs
⊑-implies-⊆ []      = []
⊑-implies-⊆ (a ∷ p) = here ∷ (⊆-wkn (⊑-implies-⊆ p))

-- The function 'take' creates a prefix list
take-is-⊑ : (as : List A) -> (∀ n -> take n as ⊑ as)
take-is-⊑ as       zero    = []
take-is-⊑ []       (suc n) = []
take-is-⊑ (x ∷ as) (suc n) = x ∷ take-is-⊑ as n

-- Suffix
-- The first list is a suffix of the second
data _⊒_ : List A -> List A -> Set where
  []  : as ⊒ as
  _∷_ : (a : A) -> as ⊒ bs -> as ⊒ (a ∷ bs)

-- also a type of sublist
⊒-implies-⊆ : as ⊒ bs -> as ⊆ bs
⊒-implies-⊆ []      = ⊆-refl _
⊒-implies-⊆ (a ∷ p) = ⊆-wkn (⊒-implies-⊆ p)

-- And functorial
map-respects : (f : A -> B) -> as ⊑ bs -> map f as ⊑ map f bs
map-respects f []      = []
map-respects f (a ∷ p) = f a ∷ map-respects f p

wkn-⊒ : (a ∷ as) ⊒ bs -> as ⊒ bs
wkn-⊒ {a = a} [] = a ∷ []
wkn-⊒ (a ∷ p)    = a ∷ wkn-⊒ p

-- 'Drop' creates a suffix list, but expressed a little more generally than before
drop-is-⊒ : (as : List A) -> (∀ n -> as ⊒ bs -> drop n as ⊒ bs)
drop-is-⊒ as       zero    p = p
drop-is-⊒ []       (suc n) p = p
drop-is-⊒ (x ∷ as) (suc n) p = drop-is-⊒ as n (wkn-⊒ p)

drop-is-⊆ : (as : List A) -> (∀ n -> as ⊆ bs -> drop n as ⊆ bs)
drop-is-⊆ [] zero p = p
drop-is-⊆ [] (suc n) p = p
drop-is-⊆ (x ∷ as) zero p = p
drop-is-⊆ (x ∷ as) (suc n) (y ∷ p) = drop-is-⊆ as n p

drop-take-⊆ : (n m : ℕ)(as : List A) -> drop n (take m as) ⊆ as
drop-take-⊆ n m as = drop-is-⊆ _ n (⊑-implies-⊆ (take-is-⊑ as m))



















---
