module CategoryBasics where

-- set of objects
-- set of arrows between those objects
-- identiy arrow for all objects: points from an object to itself
-- composition of arrows: if we have a -> b and b -> c, then we must have a -> c
-- arrow composition is associative: (a -> b) -> c === a -> (b -> c) (sort of, but we need a compositon operation)

open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Empty

-- in general categories can be over Set_n
record Category : Set₁ where 
  field 
    object : Set
    arrow : object -> object -> Set -- this is an ordered relation between objects, it's more general than just functions between objects
    id : ∀ a -> arrow a a -- for all objects, a, there is an arrow from a to a
    compose :  ∀ {a b c} -> (f : arrow b c) -> (g : arrow a b) -> arrow a c -- think of this as "f after g"

    -- laws
    -- using ≡ means we will need to postulate things! For example ≡ isn't defined if arrows are functions
    id-law-left  : ∀ a b -> (f : arrow a b) -> compose f (id a) ≡ f
    id-law-right : ∀ a b -> (f : arrow a b) -> compose (id b) f ≡ f
    assoc-law : ∀ {a b c d} 
            -> (f : arrow a b) 
            -> (g : arrow b c) 
            -> (h : arrow c d) 
            -> compose (compose h g) f  ≡ compose h (compose g f)

  _∘_ : ∀ {a b c} -> (f : arrow b c) -> (g : arrow a b) -> arrow a c
  _∘_ = compose 

open import Data.Unit
open import Data.Nat
open import Data.Nat.Properties

-- single object
-- arrows are natural numbers
-- composition is addition
addition-monoid-category : Category
addition-monoid-category =  record
  { object = ⊤
  ; arrow = λ x y -> ℕ
  ; id = λ a -> 0
  ; compose = λ f g -> f + g
  ; id-law-left = λ a b f -> +-identityʳ f
  ; id-law-right = λ a b f -> refl
  ; assoc-law = λ f g h -> +-assoc h g f
  }

open import monoid.MonoidBasics
monoid-category : Monoid -> Category
monoid-category M = record
  { object = ⊤
  ; arrow = λ x y -> type
  ; id = λ a -> ε
  ; compose = _⊕_
  ; id-law-left = λ a b -> idL 
  ; id-law-right = λ a b -> idR
  ; assoc-law = λ f g h → assoc h g f
  } 
    where open Monoid M -- open this specific monoid so we can use its functions

-- leq-category : Category
-- leq-category = record
--   { object = ℕ
--   ; arrow = λ x y -> x ≤ y
--   ; id = id'
--   ; compose = λ f g -> ≤-trans g f
--   ; id-law-left = λ a b f → id-law-left' f -- id-law-left'
--   ; id-law-right = id-law-right'
--   ; assoc-law = {!   !} 
--   }
--     where
--       id' :  ∀ x -> x ≤ x 
--       id' zero = z≤n
--       id' (suc x) = s≤s (id' x)

--       id-law-left' : {a b : ℕ} -> (f : a ≤ b) -> ≤-trans (id' a) f ≡ f
--       id-law-left' z≤n = refl
--       id-law-left' (s≤s f) = cong s≤s (id-law-left' f)

--       id-law-right' : (a b : ℕ) -> (f : a ≤ b) -> ≤-trans f (id' b) ≡ f
--       id-law-right' = {!   !}

--       assoc-law' : {a b c d : ℕ} -> (f : a ≤ b) ->  (g : b ≤ c) -> (h : c ≤ d) -> ≤-trans (≤-trans f g) h ≡ ≤-trans f (≤-trans g h)
--       assoc-law' = {!   !}

singleton-category : Category
singleton-category = record
  { object = ⊤
  ; arrow = λ x y → ⊤
  ; id = λ a → tt
  ; compose = λ f g → tt
  ; id-law-left = λ a b f → refl
  ; id-law-right = λ a b f → refl
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
  ; id-law-left = λ a b f → ⊥-elim a
  ; id-law-right = λ a b f → ⊥-elim a
  ; assoc-law = λ {a} f g h → ⊥-elim a
  }

opposite-category : (𝓒 : Category ) -> Category
opposite-category 𝓒 = record
  { object       = object
  ; arrow        = λ x y → arrow y x
  ; id           = λ a → id a
  ; compose      = λ f g → compose g f
  ; id-law-left  = λ a b f → id-law-right b a f
  ; id-law-right = λ a b f → id-law-left b a f
  ; assoc-law    = λ f g h → sym (assoc-law h g f)
  }
    where
      open Category 𝓒
    

