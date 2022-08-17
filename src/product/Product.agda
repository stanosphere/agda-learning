{-# OPTIONS --type-in-type #-}

module product.Product where

open import CategoryBasics
-- open import functor.Functors renaming (functor-composition to _|+|_)
-- open import NaturalTransformation
open import Relation.Binary.PropositionalEquality

-- product of A, B
-- identify it, name proj fields
-- what if there are others

record Product {𝓒 : Category} (A B : Category.object 𝓒) : Set where
    open Category 𝓒

    field
        A×B   : object
        π₁    : arrow A×B A
        π₂    : arrow A×B B
        <_,_> : {Y : object}(f₁ : arrow Y A)(f₂ : arrow Y B) -> arrow Y A×B

        law-π₁ : ∀ {Y} -> (f₁ : arrow Y A)(f₂ : arrow Y B) -> (π₁ ∘ < f₁ , f₂ >) ≡ f₁
        law-π₂ : ∀ {Y} -> (f₁ : arrow Y A)(f₂ : arrow Y B) -> (π₂ ∘ < f₁ , f₂ >) ≡ f₂
        unique : ∀ {Y} -> (g : arrow Y A×B) -> < π₁ ∘ g , π₂ ∘ g > ≡ g

open import Data.Product

SET-product : (A B : Set) -> Product {SET} A B
SET-product A B = record
  { A×B = A × B
  ; π₁ = λ { (n , _) -> n }
  ; π₂ = λ { (_ , b) -> b }
  ; <_,_> = λ f₁ f₂ x → f₁ x , f₂ x
  ; law-π₁ = λ f₁ f₂ → refl
  ; law-π₂ = λ f₁ f₂ → refl
  ; unique = λ g → refl
  }
