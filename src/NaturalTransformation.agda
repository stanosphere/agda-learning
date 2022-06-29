module NaturalTransformation where

open import CategoryBasics
open Category
open import functor.Functors
open Functor
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

-- F[X] --F[f]--> F[Y]
--  |              |
--  | η[X]         | η[Y]
--  |              |
--  ˅              ˅ 
-- G[X] --G[f]--> G[Y]

-- Takes objects in 𝓒 to arrows in 𝓓
record NaturalTransformation {𝓒 𝓓 : Category} (𝓕 𝓖 : Functor 𝓒 𝓓) : Set where
  field
    η : (a : object 𝓒) -> arrow 𝓓 (object_map 𝓕 a) (object_map 𝓖 a)
    commutative-law : { x y : object 𝓒 } -> { f : arrow 𝓒 x y } ->
                      compose 𝓓 (η y) (arrow_map 𝓕 f) ≡ compose 𝓓 (arrow_map 𝓖 f) (η x)

 