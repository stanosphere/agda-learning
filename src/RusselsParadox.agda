{-# OPTIONS --type-in-type #-}

module RusselsParadox where

open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Sum

variable
  A B : Set

data Zet : Set where
  Z : (I : Set) -> (I -> Zet) -> Zet

∅ : Zet
∅ = Z ⊥ λ ()

[∅] : Zet
[∅] = Z ⊤ λ _ -> ∅

[∅,[∅]] : Zet
[∅,[∅]] = Z Bool (λ b -> if b then ∅ else [∅])

record Fiber (f : A -> B)(b : B) : Set where
  constructor F
  field
    a : A
    fiber : b ≡ f a

_∈_ : Zet -> Zet -> Set
a ∈ Z I f = Fiber f a

_∉_ : Zet → Zet → Set
a ∉ b = (a ∈ b) → ⊥

-- set of all sets
-- Σ Zet (λ a -> a ∉ a)
--   All the sets that exists, such that the set (a) doesn't contain itself
R : Zet
R = Z (∃ (λ a -> a ∉ a)) proj₁

∈-implies-∉ : ∀ {X} -> X ∈ R -> X ∉ X
∈-implies-∉ (F (a , p) refl) = p

∉-implies-∈ : ∀ {X} -> X ∉ X -> X ∈ R
∉-implies-∈ {X} p = F (X , p) refl

R∉R : R ∉ R
R∉R p = ∈-implies-∉ p p

R∈R : R ∈ R
R∈R = ∉-implies-∈ R∉R

contradiction : ⊥
contradiction = R∉R R∈R
