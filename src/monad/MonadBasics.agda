{-# OPTIONS --type-in-type #-}

module monad.MonadBasics where

open import CategoryBasics
open Category hiding (_∘_)
open import functor.Functors
open Functor
open import NaturalTransformation

-- a monad is a triple on category C consisting of
--   * an endofunctor, T, in C
--   * a natural transformation from the identity functor in C, 1_c to T, η: 1_c -> T
--   * a natrual transformation from T compose T to T, μ: T ∘ T -> T
-- There are also some laws!
-- but for now I'll see if I can write down a lawless monad

record LawlessMonad { 𝓒 : Category } : Set where
  field
    T : Functor 𝓒 𝓒
    η : NaturalTransformation id-functor T
    μ : NaturalTransformation (functor-composition T T) T
       
