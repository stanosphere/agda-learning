module Inequalities where

open import Data.Nat 
open import Data.Product
open import Relation.Binary.PropositionalEquality

≤-refl : ∀ n -> n ≤ n
≤-refl zero    = z≤n
≤-refl (suc n) = s≤s (≤-refl n)

ineq-lemma-1 : ∀ {x y : ℕ}(z : ℕ) -> x > y -> z + x > z + y 
ineq-lemma-1 zero    a>b = a>b
ineq-lemma-1 (suc z) a>b = s≤s (ineq-lemma-1 z a>b)

ineq-lemma-2 : ∀ {n : ℕ} -> ∃ (λ m -> m > n)
ineq-lemma-2 { n } = 1 + n , s≤s (≤-refl n)
