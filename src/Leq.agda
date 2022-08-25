module Leq where

open import CategoryBasics
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality

LEQ : Category
LEQ = record
  { object       = ℕ
  ; arrow        = _≤_
  ; id           = id'
  ; compose      = λ f g -> ≤-trans g f
  ; id-law-left  = id-law-left'
  ; id-law-right = id-law-right'
  ; assoc-law    = assoc-law'
  }
    where
      id' :  ∀ x -> x ≤ x
      id' zero = z≤n
      id' (suc x) = s≤s (id' x)

      id-law-left' : {a b : ℕ} -> (f : a ≤ b) -> ≤-trans (id' a) f ≡ f
      id-law-left' z≤n = refl
      id-law-left' (s≤s f) = cong s≤s (id-law-left' f)

      id-law-right' : {a b : ℕ} -> (f : a ≤ b) -> ≤-trans f (id' b) ≡ f
      id-law-right' z≤n = refl
      id-law-right' (s≤s f) = cong s≤s (id-law-right' f)

      assoc-law' : {a b c d : ℕ} -> (f : a ≤ b)(g : b ≤ c)(h : c ≤ d) -> ≤-trans f (≤-trans g h) ≡ ≤-trans (≤-trans f g) h
      assoc-law' z≤n g h = refl
      assoc-law' (s≤s f) (s≤s g) (s≤s h) = cong s≤s (assoc-law' f g h)


open import product.Product

leq-product : (n m : ℕ) -> Product {LEQ} n m
leq-product n m = record
  { A×B    = n ⊓ m
  ; π₁     = minˡ n m
  ; π₂     = minʳ n m
  ; <_,_>  = smallest
  ; law-π₁ = law-π₁
  ; law-π₂ = law-π₂
  ; unique = unique
  }
  where
    minˡ : (n m : ℕ) -> n ⊓ m ≤ n
    minˡ zero    m       = z≤n
    minˡ (suc n) zero    = z≤n
    minˡ (suc n) (suc m) = s≤s (minˡ n m)

    minʳ : (n m : ℕ) -> n ⊓ m ≤ m
    minʳ zero    m       = z≤n
    minʳ (suc n) zero    = z≤n
    minʳ (suc n) (suc m) = s≤s (minʳ n m)

    smallest : {n m o : ℕ} → o ≤ n → o ≤ m → o ≤ n ⊓ m
    smallest z≤n          q  = z≤n
    smallest (s≤s p) (s≤s q) = s≤s (smallest p q)

    law-π₁ : {o n m : ℕ} (f₁ : o ≤ n) (f₂ : o ≤ m) → ≤-trans (smallest f₁ f₂) (minˡ n m) ≡ f₁
    law-π₁ z≤n          g  = refl
    law-π₁ (s≤s f) (s≤s g) = cong s≤s (law-π₁ f g)

    law-π₂ : {o n m : ℕ} (f₁ : o ≤ n) (f₂ : o ≤ m) → ≤-trans (smallest f₁ f₂) (minʳ n m) ≡ f₂
    law-π₂ z≤n      z≤n    = refl
    law-π₂ (s≤s f) (s≤s g) = cong s≤s (law-π₂ f g)

    unique : {n m o : ℕ} (g : o ≤ n ⊓ m) → smallest (≤-trans g (minˡ n m)) (≤-trans g (minʳ n m)) ≡ g
    unique {zero}  {m   }  z≤n     = refl
    unique {suc n} {zero}  z≤n     = refl
    unique {suc n} {suc m} z≤n     = refl
    unique {suc n} {suc m} (s≤s g) = cong s≤s (unique g)
