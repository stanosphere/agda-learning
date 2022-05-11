module Basics where

Type : Set₁
Type = Set

data Bool : Type where
  true : Bool
  false : Bool

data List (A : Set) : Set where
  []   : List A
  _::_ : A -> List A -> List A

open import Data.Nat

data Vec (A : Type) : ℕ -> Type where
  []   : Vec A 0
  _::_ : ∀ {n} -> A -> Vec A n -> Vec A (1 + n)

head : ∀ {A n} -> Vec A (1 + n) -> A
head (x :: v) = x

open import Data.Product

headhead : ∀ {A n} -> Vec A (2 + n) -> A × A
headhead (x :: (y :: xs)) = x , y

data Even : ℕ -> Type where
  zero-even : Even 0
  succ-succ-even : ∀ {n} -> Even n -> Even (suc (suc n))

open import Data.Empty

_++_ : ℕ -> ℕ -> ℕ
zero ++ m = m
suc n ++ m = suc (n ++ m)

_**_ : ℕ -> ℕ -> ℕ
zero ** m = 0
suc n ** m = m ++ (n ** m)

Not : Type -> Type
Not A = A -> ⊥

Odd : ℕ -> Type
Odd n = Not (Even n)

odd1 : Odd 11
odd1 (succ-succ-even (succ-succ-even (succ-succ-even (succ-succ-even (succ-succ-even ())))))

odd13 : Odd 11
odd13 p = odd1 p

ex : Even 4
ex = succ-succ-even (succ-succ-even zero-even)

open import Data.Sum
open import Relation.Binary.PropositionalEquality

forwards : ∀ {n} -> Even n -> ∃ (λ m -> (m * 2 ≡ n))
forwards p = {!   !}

backwards : ∀ {n} -> ∃ (λ m -> (m * 2 ≡ n)) -> Even n
backwards (fst , snd) = {!   !}

ex1 : ∀ {n} -> Even n -> Even (n * n)
ex1 zero-even = zero-even
ex1 (succ-succ-even p) = {! ex1 p  !}

ex2 : ∀ {n} -> Even (n * n) -> Even n
ex2 p = {!   !}
