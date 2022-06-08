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

ineq-lemma-3 : ∀ {x y : ℕ} -> x > 0 -> y > 0 -> x * y > 0
ineq-lemma-3 {a} {b} a>0 y>0 = {!   !}

-- transistivity
ineq-lemma-4 : ∀ {x y z : ℕ} -> x > y -> y > z -> x > z
ineq-lemma-4 {suc a} {suc b} {zero } (s≤s a>b) (s≤s b>c) = s≤s z≤n
ineq-lemma-4 {suc a} {suc b} {suc c} (s≤s a>b) (s≤s b>c) = s≤s (ineq-lemma-4 {a} {b} {c} a>b b>c)

