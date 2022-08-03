{-# OPTIONS --type-in-type #-}

module monad.MonadBasics where

open import CategoryBasics
-- open Category 
open import functor.Functors renaming (functor-composition to _|+|_)
open Functor 
open import NaturalTransformation
open import Relation.Binary.PropositionalEquality

-- a monad is a triple on category C consisting of
--   * an endofunctor, T, in C
--   * a natural transformation from the identity functor in C, 1_c to T, η: 1_c -> T
--   * a natrual transformation from T compose T to T, μ: T ∘ T -> T
-- There are also some laws!
-- but for now I'll see if I can write down a lawless monad

record LawlessMonad { 𝓒 : CategoryBasics.Category } : Set where
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

record Monad { 𝓒 : CategoryBasics.Category  } : Set where
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
  field 
    id-law-right : ∀ x -> join.η x ∘ return.η (object-map T x) ≡ id (object-map T x)
    id-law-left : ∀ x -> join.η x ∘ arrow-map T (return.η x) ≡ id (object-map T x)
    -- each side of the assoc-law takes T |+| T |+| T -> T
    -- one side unests the outer T's first, the other unests the inner T's first
    assoc-law : ∀ x -> (join.η x) ∘ (arrow-map T (join.η x)) ≡ (join.η x) ∘ (join.η (object-map T x))

       
