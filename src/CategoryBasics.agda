{-# OPTIONS --type-in-type #-}

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module CategoryBasics where

-- set of objects
-- set of arrows between those objects
-- identiy arrow for all objects: points from an object to itself
-- composition of arrows: if we have a -> b and b -> c, then we must have a -> c
-- arrow composition is associative: (a -> b) -> c === a -> (b -> c) (sort of, but we need a compositon operation)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty
open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties
open import monoid.MonoidBasics
open import monoid.MonoidMorphisms

-- in general categories can be over Set_n
record Category : Set where
  field
    object : Set
    arrow : object -> object -> Set -- this is an ordered relation between objects, it's more general than just functions between objects
    id : ∀ a -> arrow a a -- for all objects, a, there is an arrow from a to a
    compose :  ∀ {a b c} -> (f : arrow b c) -> (g : arrow a b) -> arrow a c -- think of this as "f after g"

    -- laws
    -- using ≡ means we will need to postulate things! For example ≡ isn't defined if arrows are functions
    id-law-left  : ∀ {a b} -> (f : arrow a b) -> compose f (id a) ≡ f
    id-law-right : ∀ {a b} -> (f : arrow a b) -> compose (id b) f ≡ f
    assoc-law : ∀ {a b c d}
            -> (f : arrow a b)
            -> (g : arrow b c)
            -> (h : arrow c d)
            -> compose (compose h g) f ≡ compose h (compose g f)

  _∘_ : ∀ {a b c} -> (f : arrow b c) -> (g : arrow a b) -> arrow a c
  _∘_ = compose

-- single object
-- arrows are natural numbers
-- composition is addition
addition-monoid-category : Category
addition-monoid-category =  record
  { object = ⊤
  ; arrow = λ x y -> ℕ
  ; id = λ a -> 0
  ; compose = λ f g -> f + g
  ; id-law-left = λ f -> +-identityʳ f
  ; id-law-right = λ f -> refl
  ; assoc-law = λ f g h -> +-assoc h g f
  }

monoid-category : Monoid -> Category
monoid-category M = record
  { object = ⊤
  ; arrow = λ x y -> type
  ; id = λ a -> ε
  ; compose = _⊕_
  ; id-law-left = idL
  ; id-law-right = idR
  ; assoc-law = λ f g h → assoc h g f
  }
    where open Monoid M -- open this specific monoid so we can use its functions

singleton-category : Category
singleton-category = record
  { object = ⊤
  ; arrow = λ x y → ⊤
  ; id = λ a → tt
  ; compose = λ f g → tt
  ; id-law-left = λ f → refl
  ; id-law-right = λ f → refl
  ; assoc-law = λ f g h → refl
  }

-- vacuous truth
-- all predicates on an empty set are true
empty-category : Category
empty-category = record
  { object = ⊥
  ; arrow = λ ()
  ; id = λ ()
  ; compose = λ {a} f g → ⊥-elim a
  ; id-law-left = λ {a} f → ⊥-elim a
  ; id-law-right = λ {a} f → ⊥-elim a
  ; assoc-law = λ {a} f g h → ⊥-elim a
  }

-- this generally isn't a functor
-- (a -> b, b -> c, a -> c) ==> (b -> a, c -> b, c -> a)
opposite-category : (𝓒 : Category ) -> Category
opposite-category 𝓒 = record
  { object       = object
  ; arrow        = λ x y → arrow y x
  ; id           = λ a → id a
  ; compose      = λ f g → compose g f
  ; id-law-left  = λ {a} {b} f → id-law-right {b} {a} f
  ; id-law-right = λ {a} {b} f → id-law-left {b} {a} f
  ; assoc-law    = λ f g h → sym (assoc-law h g f)
  }
    where
      open Category 𝓒

-- category of agda types
SET : Category
SET = record
  { object       = Set
  ; arrow        = λ X Y -> (X -> Y)
  ; id           = λ A -> (λ a -> a)
  ; compose      = λ f g a -> f (g a)
  ; id-law-left  = λ f -> refl
  ; id-law-right = λ f -> refl
  ; assoc-law    = λ f g h -> refl
  }

-- _≐_ : {a b : Monoid}(f g : MonoidMorphism a b) → Set
-- _≐_ {a} f g = ∀ {x : Monoid.type a} -> map f x ≡ map g x
--   where open MonoidMorphism

-- id-law-left : {a b : Monoid} (f : MonoidMorphism a b)
--             -> combine-morphism f (identity-morphism a) ≐ f
-- id-law-left f = refl

-- objects are monoids, arrows, are monoid morphisms
-- MONOID : Category
-- MONOID = record
--   { object       = Monoid
--   ; arrow        = MonoidMorphism
--   ; id           = identity-morphism
--   ; compose      = combine-morphism
--   ; id-law-left  = id-law-left'
--   ; id-law-right = {!   !}
--   ; assoc-law    = {!   !}
--   }
--   where
--     id-law-left' : {a b : Monoid} (f : MonoidMorphism a b) -> combine-morphism f (identity-morphism a) ≡ f
--     id-law-left' {a} {b} record { map = map ; idPreserve = idPreserve ; combPreserve = combPreserve } = {!   !}
--       -- where
--       --   open Monoid a renaming (ε to ψ ; _⊕_ to _⊙_)
--       --   open Monoid b renaming (ε to φ ; _⊕_ to _⊗_)
--       --   open MonoidMorphism f renaming (map to mapF ; idPreserve to idPreserveF ; combPreserve to combPreserveF)
--       --   open MonoidMorphism (identity-morphism a) renaming (map to mapG ; idPreserve to idPreserveG ; combPreserve to combPreserveG)
