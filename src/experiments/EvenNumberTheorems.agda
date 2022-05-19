module EvenNumberTheorems where
  
open import Data.Nat
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
-- https://stackoverflow.com/questions/42357572/agda-product-of-even-numbers-is-even

data Even : ℕ -> Set where
  zEven : Even 0
  sEven : {n : ℕ} -> Even n -> Even (suc (suc n))

data GreaterThanOne : ℕ -> Set where
  one : GreaterThanOne 1
  sGT1 : {n : ℕ} -> GreaterThanOne n -> GreaterThanOne (suc n)

sum-of-evens : ∀ {n m} -> Even n -> Even m -> Even (n + m)
sum-of-evens zEven     y = y
sum-of-evens (sEven x) y = sEven (sum-of-evens x y)

product-of-evens : ∀ {n m : ℕ} -> Even n -> Even m -> Even (n * m)
product-of-evens zEven y     = zEven
product-of-evens (sEven x) y =
  let
    -- a : Even (n * m)
    a = product-of-evens x y
    -- b : Even (m + n * m)
    b = sum-of-evens y a
    -- c : Even (m + (m + n * m))
    c =   sum-of-evens y b
  in c

square-of-even : ∀ {n} -> Even n -> Even (n * n)
square-of-even x = product-of-evens x x

-- pen and paper proof uses contradiction
square-of-even-converse : ∀ {n} -> Even (n * n) -> Even n
square-of-even-converse x_squared = {!   !}

add-two-numbers : (n : ℕ) -> Even (n + n)
add-two-numbers zero = zEven
add-two-numbers (suc x) = 
  let
    a : Even (suc (suc (x + x)))
    a = sEven (add-two-numbers x)

    b : suc (suc (x + x)) ≡ suc x + suc x
    b = lemma-suc-2 x
    
    res : Even (suc x + suc x)
    res = subst Even b a
  in res
  where 
    lemma-suc-shuffle : (p q : ℕ) -> p + suc q ≡ suc (p + q)
    lemma-suc-shuffle zero q = refl
    lemma-suc-shuffle (suc p) q = cong suc (lemma-suc-shuffle p q)
    lemma-suc-shuffle-2 : (p q : ℕ) -> (suc p) + (suc q) ≡ suc (suc (p + q))
    lemma-suc-shuffle-2 p q = 
      begin 
        (suc p) + (suc q)
          ≡⟨ refl ⟩ 
        suc (p + suc q)
          ≡⟨ cong suc (lemma-suc-shuffle p q) ⟩ 
        suc (suc (p + q)) 
      ∎ 
    lemma-suc-2 : (p : ℕ) -> suc (suc (p + p)) ≡ (suc p) + (suc p)
    lemma-suc-2 p = sym (lemma-suc-shuffle-2 p p)

even-mult : ∀ {n} -> Even n -> (m : ℕ) -> Even (n * m)
even-mult zEven y = zEven
even-mult (sEven x) y = {!   !}

power-of-even : ∀ {n k} -> Even n -> GreaterThanOne k -> Even (n ^ k)
power-of-even x one = subst Even {!   !} x
power-of-even x (sGT1 y) = {!   !}
  where
    mult-identity-lemma : { n : ℕ } -> n ≡ n * 1
    mult-identity-lemma { zero } = refl
    mult-identity-lemma { suc x } = cong suc (mult-identity-lemma {x})
 