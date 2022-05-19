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

product-of-evens : ∀ {n m} -> Even n -> Even m -> Even (n * m)
product-of-evens zEven y     = zEven
product-of-evens (sEven x) y = sum-of-evens y (sum-of-evens y (product-of-evens x y))
-- In the above I have
-- x : Even n
-- y : Even m
-- And need to show
-- Even (m + (m + n * m))

-- Whilst the above implementation is obviously correct it's perhaps not massively readable
-- I would like to do something like
--   val a = product-of-evens x y
--   val b = sum-of-evens y a
--   val c = sum-of-evens y b
--   return c

-- is there a syntax for the above???

square-of-even : ∀ {n} -> Even n -> Even (n * n)
square-of-even x = product-of-evens x x

-- pen and paper proof uses contradiction
square-of-even-converse : ∀ {n} -> Even (n * n) -> Even n
square-of-even-converse x_squared = {!   !}

add-two-numbers : (n : ℕ) -> Even (n + n)
add-two-numbers zero = zEven
add-two-numbers (suc x) = {!   !} 

even-mult : ∀ {n} -> Even n -> (m : ℕ) -> Even (n * m)
even-mult zEven y = zEven
even-mult (sEven x) y = {!   !}

power-of-even : ∀ {n k} -> Even n -> GreaterThanOne k -> Even (n ^ k)
power-of-even x one = {!   !}
power-of-even x (sGT1 y) = {!   !}

