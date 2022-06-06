module Inequalities where

open import Data.Nat 

ineq-lemma-1 : ∀ { x y z : ℕ } -> x > y -> x + z > y + z
-- goal: a + zero > b + zero
ineq-lemma-1 {a} {b} {zero}  a>b = {!   !}
-- goal: a + suc c > b + suc c
ineq-lemma-1 {a} {b} {suc c} a>b = {!   !}
