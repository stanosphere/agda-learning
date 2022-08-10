{-# OPTIONS --type-in-type #-}

module monad.MonadBasics where

open import CategoryBasics
open import functor.Functors renaming (functor-composition to _|+|_)
open import NaturalTransformation
open import Relation.Binary.PropositionalEquality

-- a monad is a triple on category C consisting of
--   * an endofunctor, T, in C
--   * a natural transformation from the identity functor in C, 1_c to T, η: 1_c -> T
--   * a natrual transformation from T compose T to T, μ: T ∘ T -> T
-- There are also some laws!
-- but for now I'll see if I can write down a lawless monad

record LawlessMonad { 𝓒 : Category } : Set where
  field
    T : Functor 𝓒 𝓒
    η : NaturalTransformation id-functor T -- return
    μ : NaturalTransformation (T |+| T) T -- join

-- the monad laws are basically the same as the monoid laws
-- first we have associativity
-- μ ∘ Tμ === μ ∘ μT
-- and then the two identity laws
-- μ ∘ Tη === 1 (1 identity naturl transformation on T)
-- μ ∘ ηT === 1 (1 identity naturl transformation on T)

record Monad { 𝓒 : Category  } : Set where
  field
    T : Functor 𝓒 𝓒
    η : NaturalTransformation id-functor T
    μ : NaturalTransformation (T |+| T) T
    -- laws
    -- id-law-right: join after return (x) and join after map return arte the same
    -- id-law-right : μ 
  module join = NaturalTransformation.NaturalTransformation μ 
  module return = NaturalTransformation.NaturalTransformation η 
  open Category 𝓒
  open Functor T renaming (object-map to T₀; arrow-map to T₁)

  field 
    id-law-right : ∀ x -> join.η x ∘ return.η (T₀ x) ≡ id (T₀ x)
    id-law-left : ∀ x -> join.η x ∘ T₁ (return.η x) ≡ id (T₀ x)
    -- each side of the assoc-law takes T |+| T |+| T -> T
    -- one side unests the outer T's first, the other unests the inner T's first
    assoc-law : ∀ x -> (join.η x) ∘ (T₁ (join.η x)) ≡ (join.η x) ∘ (join.η (T₀ x))

MAYBE-Monad : Monad {SET}
MAYBE-Monad = record
  { T = MAYBE
  ; η = maybe-pure
  ; μ = maybe-flatten
  ; id-law-right = λ A → refl
  ; id-law-left = λ A → funex id-law-left'
  ; assoc-law = λ A → funex assoc-law'
  }
  where
    open import Data.Maybe
    maybe-pure : NaturalTransformation id-functor MAYBE
    maybe-pure = record { η = λ A a → just a ; commutative-law = refl }

    flatten : {a : Set} -> Maybe (Maybe a) -> Maybe a
    flatten (just x) = x
    flatten nothing = nothing

    flatten-law : {A B : Set} -> {f : A -> B} -> (a : Maybe (Maybe A)) -> flatten (map (map f) a) ≡ map f (flatten a)
    flatten-law (just mma) = refl
    flatten-law nothing = refl

    maybe-flatten : NaturalTransformation (MAYBE |+| MAYBE) MAYBE
    maybe-flatten = record { η = λ A a → flatten a ; commutative-law = funex flatten-law  }

    id-law-left' : {A : Set} -> (a : Maybe A) -> flatten (map just a) ≡ a
    id-law-left' (just x) = refl -- flatten (map just (just x)) ≡ just x
    id-law-left' nothing = refl  -- flatten (map just nothing) ≡ nothing

    assoc-law' : {A : Set} -> (a : Maybe (Maybe (Maybe A))) -> flatten (map flatten a) ≡ flatten (flatten a)
    assoc-law' (just mmma) = refl -- flatten (map flatten (just mmma)) ≡ flatten (flatten (just mmma))
    assoc-law' nothing = refl     -- flatten (map flatten nothing) ≡ flatten (flatten nothing)
       