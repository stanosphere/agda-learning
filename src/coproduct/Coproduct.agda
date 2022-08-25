{-# OPTIONS --type-in-type #-}

module coproduct.Coproduct where

open import CategoryBasics
open import functor.Functors
open import Relation.Binary.PropositionalEquality

record Coproduct {𝓒 : Category} (A B : Category.object 𝓒) : Set where
    open Category 𝓒

    field
        A+B     : object
        inj₁    : arrow A A+B
        inj₂    : arrow B A+B
        <_+_> : {Y : object}(f₁ : arrow A Y)(f₂ : arrow B Y) -> arrow A+B Y

        law-inj₁ : ∀ {Y} -> (f₁ : arrow A Y)(f₂ : arrow B Y) -> ( < f₁ + f₂ > ∘ inj₁) ≡ f₁
        law-inj₂ : ∀ {Y} -> (f₁ : arrow A Y)(f₂ : arrow B Y) -> ( < f₁ + f₂ > ∘ inj₂) ≡ f₂
        unique : ∀ {Y} -> (g : arrow A+B Y ) -> < g ∘ inj₁ +  g ∘ inj₂ > ≡ g

open import Data.Sum renaming ( inj₁ to i₁ ;  inj₂ to i₂ )

SET-coproduct : (A B : Set) -> Coproduct {SET} A B
SET-coproduct A B = record
  { A+B = A ⊎ B
  ; inj₁ = i₁
  ; inj₂ = i₂
  ; <_+_> = λ f₁ f₂ → λ { (i₁ l) -> f₁ l ; (i₂ r) -> f₂ r }
  ; law-inj₁ = λ f₁ f₂ → refl
  ; law-inj₂ = λ f₁ f₂ → refl
  ; unique = λ g → funex (λ { (i₁ l) -> refl ; (i₂ r) -> refl })
  }
