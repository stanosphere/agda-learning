module BasicInduction where

open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

sum : ℕ -> ℕ
sum 0 = 0
sum (suc a) = (suc a) + sum a

summation-formula-proof : (n : ℕ) -> 2 * sum n ≡ n * (n + 1)
summation-formula-proof zero = refl
summation-formula-proof (suc a) = begin 
  2 * (sum (suc a))                 ≡⟨ refl ⟩ 
  2 * (suc a + sum a)               ≡⟨ *-distribˡ-+ 2 (suc a) (sum a) ⟩ 
  (2 * suc a) + (2 * sum a)         ≡⟨ cong (λ u -> (2 * suc a) + u) (summation-formula-proof a) ⟩ 
  -- just careful but "obvious" algebra below here
  (2 * suc a) + (a * (a + 1))       ≡⟨ refl ⟩ 
  2 * (1 + a) + a * (a + 1)         ≡⟨ cong (λ u -> 2 * (1 + a) + a * (u)) (+-comm a 1) ⟩ 
  2 * (1 + a) + a * (1 + a)         ≡⟨ sym (*-distribʳ-+ (1 + a) 2 a ) ⟩ 
  (2 + a) * (1 + a)                 ≡⟨ *-comm (2 + a) (1 + a)  ⟩ 
  (1 + a) * (2 + a)                 ≡⟨ refl ⟩ 
  -- for me the above is proof enough but agda needs things to be in terms of suc I'm afraid
  (1 + a) * (1 + 1 + a)             ≡⟨ cong (λ u -> (1 + a) * (1 + u)) (+-comm 1 a) ⟩ 
  (1 + a) * (1 + a + 1)             ≡⟨ refl ⟩ 
  (1 + a) * ((1 + a) + 1)           ≡⟨ *-distribˡ-+ (1 + a) (1 + a) 1 ⟩ 
  (1 + a) * (1 + a) + (1 + a) * 1   ≡⟨ cong  (λ u -> (1 + a) * (1 + a) + u) (cong (suc) (sym (mult-id-lemma a))) ⟩ 
  (1 + a) * (1 + a) + (1 + a)       ≡⟨ refl ⟩
  (suc a) * (suc a) + (suc a)       ≡⟨ cong  (λ u -> (suc a) * (suc a) + u) (cong (suc) (mult-id-lemma a))  ⟩ 
  (suc a) * (suc a) + (suc a) * 1   ≡⟨ sym (*-distribˡ-+ (suc a) (suc a) 1) ⟩ 
  (suc a) * ((suc a) + 1)           ∎
    where
      mult-id-lemma : (n : ℕ) -> n ≡ n * 1
      mult-id-lemma zero = refl
      mult-id-lemma (suc a) = cong suc (mult-id-lemma a)
