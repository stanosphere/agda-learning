module Equals where

open import Data.Nat

variable
  A B : Set
  a b c : A
  n m o : ℕ

module OurEq where

  -- Let's revisit the definition of equality
  data Eq {A : Set} : A -> A -> Set where
    refl : {a : A} -> Eq a a

  -- Eq is an equivalence
  Eq-refl : Eq a a
  Eq-refl = refl

  Eq-sym : Eq a b -> Eq b a
  Eq-sym refl = refl

  Eq-trans : Eq a b -> Eq b c -> Eq a c
  Eq-trans refl q = q

  -- a ≡ b -> f a ≡ f b
  cong : (f : A -> B) -> Eq a b -> Eq (f a) (f b)
  cong f refl = refl

  -- Even n, and n ≡ m, then Even m
  subst : (P : A -> Set) -> Eq a b -> P a -> P b
  subst P refl q = q

  +-zero : ∀ n -> Eq n (n + 0)
  +-zero zero    = refl
  +-zero (suc n) = cong suc (+-zero n)

open import Relation.Binary.PropositionalEquality

+-zero : (n : ℕ) -> n ≡ n + 0
+-zero zero = refl
+-zero (suc n) = cong suc (+-zero n)

+-suc : (n m : ℕ) -> suc (n + m) ≡ n + suc m
+-suc zero    m                   = refl
+-suc (suc n) m rewrite +-suc n m = refl

+-comm : (n m : ℕ) -> n + m ≡ m + n
+-comm zero    m = +-zero m
+-comm (suc n) m rewrite sym (+-suc m n) | +-comm n m = refl

open ≡-Reasoning

+-assoc : (n m o : ℕ) -> (n + m) + o ≡ n + (m + o)
+-assoc zero    m o = refl
+-assoc (suc n) m o =
  begin
    (suc n + m) + o
      ≡⟨ refl ⟩
    (suc (n + m)) + o
      ≡⟨ refl ⟩
    suc ((n + m) + o)
      ≡⟨ cong suc (+-assoc n m o) ⟩
    suc (n + (m + o))
      ≡⟨ refl ⟩
    (suc n) + (m + o)
  ∎

infix 2 _≈_
_≈_ : (f g : A -> B) -> Set
f ≈ g = ∀ a -> f a ≡ g a

open import Function

fun-comp : (f g h : A -> A) -> (f ∘ g) ∘ h ≈ f ∘ (g ∘ h)
fun-comp f g h a = refl










----
