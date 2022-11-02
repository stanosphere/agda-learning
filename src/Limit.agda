{-# OPTIONS --type-in-type #-}

module Limit where

open import CategoryBasics
open Category
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Nat
open import functor.Functors
open Functor
open import Leq
import NaturalTransformation
open ≡-Reasoning

-- J index category
-- constant Functor to pick apex for candidates
-- one apex is the true limit
-- functor to pick diagrams
-- natural transformation between constant functor and diagram picking functor
-- define cone
-- which cone is best???

record Cone { 𝓒 J : Category } (F : Functor J 𝓒) : Set where
  field 
    apex : object 𝓒
    ψ : (x : object J) -> arrow 𝓒 apex (object-map F x) -- looks a lot like a NT
    -- communing condition
    condition : (x y : object J) -> (f : arrow J x y) -> compose 𝓒 (arrow-map F f) (ψ x) ≡ (ψ y)

record Cone2 {𝓒 J : Category} (F : Functor J 𝓒) : Set where
  field 
    apex : object 𝓒

  constant-functor : Functor J 𝓒 
  constant-functor = record
    { object-map = λ f → apex
    ; arrow-map = λ f → id 𝓒 apex
    ; identity-preservation = refl
    ; composition-preservation = λ f g → sym (id-law-left 𝓒 _)
    }
    
  field
    nt : NaturalTransformation.NaturalTransformation constant-functor F
    -- show commutivity condition here 

module ConeEquivalence { 𝓒 J : Category } (F : Functor J 𝓒)  where 
  -- to prove equivalence of Cone and Cone2 we need these two fellows
  forwards :    Cone F -> Cone2 F
  forwards cone  = record
    { apex = apex; 
    nt = record { 
      η = ψ ; 
      commutative-law = begin
      compose 𝓒 (ψ _) (id 𝓒 apex)    ≡⟨ id-law-left 𝓒 _ ⟩
      (ψ _)                           ≡⟨ sym (condition _ _ _) ⟩
      compose 𝓒 (arrow-map F _) (ψ _) ∎ 
      } 
    } 
    where
       open Cone cone 

  backwards : Cone2 F  -> Cone  F
  backwards cone2 = record 
    { apex = apex ;
     ψ = η ; 
     condition = λ x y f → begin
      compose 𝓒 (arrow-map F f) (η x)  ≡⟨ sym commutative-law ⟩
      compose 𝓒 (η y) (id 𝓒 apex)      ≡⟨ id-law-left 𝓒 (η y) ⟩
      η y               ∎ 
    }
    where
      open Cone2 cone2 
      open NaturalTransformation.NaturalTransformation nt

-- J is empty category
-- terminal-object-cone