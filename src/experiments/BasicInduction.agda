module BasicInduction where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat.Tactic.RingSolver
open import Data.List as List using (List; _∷_; [])

sum : ℕ -> ℕ
sum 0       = 0
sum (suc a) = (suc a) + sum a

summation-formula-proof : (n : ℕ) -> 2 * sum n ≡ n * (n + 1)
summation-formula-proof zero = refl
summation-formula-proof (suc a) = begin 
  2 * (sum (suc a))           ≡⟨ refl ⟩ 
  2 * (suc a + sum a)         ≡⟨ *-distribˡ-+ 2 (suc a) (sum a) ⟩ 
  (2 * suc a) + (2 * sum a)   ≡⟨ cong (λ u -> 2 * suc a + u) (summation-formula-proof a) ⟩ 
  -- just careful but "obvious" algebra after the induction step, is there a nice solver that can do this automatically?
  (2 * suc a) + (a * (a + 1)) ≡⟨ refl ⟩ 
  2 * (1 + a) + a * (a + 1)   ≡⟨ cong (λ u -> 2 * (1 + a) + a * u) (+-comm a 1) ⟩ 
  2 * (1 + a) + a * (1 + a)   ≡⟨ sym (*-distribʳ-+ (1 + a) 2 a ) ⟩ 
  (2 + a) * (1 + a)           ≡⟨ *-comm (2 + a) (1 + a) ⟩ 
  (1 + a) * (2 + a)           ≡⟨ refl ⟩ 
  (1 + a) * (1 + 1 + a)       ≡⟨ cong (λ u -> (1 + a) * (1 + u)) (+-comm 1 a) ⟩ 
  (1 + a) * ((1 + a) + 1)     ≡⟨ refl ⟩ 
  (suc a) * ((suc a) + 1)     ∎

summation-formula-proof' : (n : ℕ) -> 2 * sum n ≡ n * (n + 1)
summation-formula-proof' zero = refl
summation-formula-proof' (suc a) =  begin 
  2 * (sum (suc a))         ≡⟨ refl ⟩ 
  2 * (suc a + sum a)       ≡⟨ *-distribˡ-+ 2 (suc a) (sum a) ⟩ 
  (2 * suc a) + (2 * sum a) ≡⟨ cong (λ u -> 2 * suc a + u) (summation-formula-proof' a) ⟩ 
  2 * (1 + a) + a * (a + 1) ≡⟨ solve (a ∷ []) ⟩ 
  (suc a) * ((suc a) + 1)   ∎

square-formula : (n m : ℕ) -> (n + m) * (n + m) ≡ n * n + 2 * n * m + m * m
square-formula a b = solve (a ∷ b ∷ []) 

sum-powers : ℕ -> ℕ -> ℕ
sum-powers exponent 0 = 0
sum-powers exponent (suc a) = (suc a) ^ exponent + sum-powers exponent a

sum-squares : ℕ -> ℕ
sum-squares = sum-powers 2

sum-cubes : ℕ -> ℕ
sum-cubes = sum-powers 3
