module NaturalTransformation where

open import CategoryBasics
open Category hiding (_∘_)
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
    η : (a : object 𝓒) -> arrow 𝓓 (object-map 𝓕 a) (object-map 𝓖 a)
    commutative-law : {x y : object 𝓒} -> {f : arrow 𝓒 x y}
                    -> compose 𝓓 (η y) (arrow-map 𝓕 f) ≡ compose 𝓓 (arrow-map 𝓖 f) (η x)

Id : {𝓒 𝓓 : Category}(F : Functor 𝓒 𝓓) -> NaturalTransformation F F
Id {𝓒} {𝓓} F = record
  { η = λ a → id 𝓓 (object-map F a)
  ; commutative-law = λ {x} {y} {f} -> begin
      compose 𝓓 (id 𝓓 (object-map F y)) (arrow-map F f)
        ≡⟨ id-law-right 𝓓 (arrow-map F f)⟩
      arrow-map F f
        ≡⟨ sym (id-law-left 𝓓 (arrow-map F f)) ⟩
      compose 𝓓 (arrow-map F f) (id 𝓓 (object-map F x))
      ∎
  }

-- M o M -> M
-- η : (a : object 𝓒) -> arrow 𝓓 (object-map 𝓕 a) (object-map 𝓖 a)
-- commutative-law : {x y : object 𝓒} -> {f : arrow 𝓒 x y}
--                 -> compose 𝓓 (η y) (arrow-map 𝓕 f) ≡ compose 𝓓 (arrow-map 𝓖 f) (η x)

_⨁_ : {𝓒 𝓓 : Category}{F G H : Functor 𝓒 𝓓}
  -> (I : NaturalTransformation G H)
  -> (J : NaturalTransformation F G)
  -> NaturalTransformation F H
_⨁_ {𝓒} {𝓓} {F} {G} {H} I J = record
  { η = λ X → (θ X) ∘ (η X)
  ; commutative-law = λ {X} {Y} {f} -> begin
        (θ Y ∘ η Y) ∘ F[ f ]
          ≡⟨ assoc-lawD _ _ _ ⟩
        θ Y ∘ (η Y ∘ F[ f ])
          ≡⟨ cong (λ x → θ Y ∘ x) law-J ⟩
        θ Y ∘ (G[ f ] ∘ η X)
          ≡⟨ sym (assoc-lawD _ _ _) ⟩
        (θ Y ∘ G[ f ]) ∘ η X
          ≡⟨ cong (λ x -> x ∘ η X) law-I ⟩
        (H[ f ] ∘ θ X) ∘ η X
          ≡⟨ assoc-lawD _ _ _ ⟩
        (H[ f ]) ∘ (θ X ∘ η X)
        ∎
  }
  where
    open NaturalTransformation I renaming (η to θ; commutative-law to law-I)
    open NaturalTransformation J renaming (commutative-law to law-J)
    open Category 𝓓 renaming (assoc-law to assoc-lawD)
    open Functor G renaming (arrow-map to G[_])
    open Functor F renaming (arrow-map to F[_])
    open Functor H renaming (arrow-map to H[_])
















  ---
