module functor.Functors where

open import CategoryBasics
open Category
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Unit
open import Data.Empty

record Functor (𝓒 𝓓 : Category) : Set where
  field
    object_map : (X : object 𝓒) -> object 𝓓
    arrow_map : ∀ { a b : object 𝓒 } -> ( f : arrow 𝓒 a b ) -> arrow 𝓓 (object_map a) (object_map b)

    -- laws
    -- for all a in 𝓒 arrow_mapping id gets mapped to id on object_map of a
    identity-preservation : ∀ { a : object 𝓒 } -> arrow_map (id 𝓒 a) ≡ id 𝓓 (object_map a)
    -- for all objects in C, composing and then mapping is identical to mapping first and then composing
    composition-preservation :
      ∀ { a b c : object 𝓒 } -> (f : arrow 𝓒 b c) (g : arrow 𝓒 a b) -> arrow_map (compose 𝓒 f g)  ≡ compose 𝓓 ( arrow_map f ) (arrow_map g)
    
-- comparison with scala Functor
-- map : (A -> B) -> List[A] -> List[B]
-- object_map: List: Type -> Type, C = Scala type, D = Scala type
-- arrow_map: (A -> B) -> (List[A] -> List[B])

-- map(f compose g) === (map f) compose (map g)
-- map(x -> x) === identity

id-functor : { 𝓒 : Category } -> Functor 𝓒 𝓒
id-functor = record
  { object_map = λ X -> X
  ; arrow_map = λ f -> f
  ; identity-preservation = refl
  ; composition-preservation = λ f g -> refl
  } 

to-singleton : { 𝓒 : Category } -> Functor 𝓒 singleton-category
to-singleton = record
  { object_map               = λ X → tt
  ; arrow_map                = λ f → tt
  ; identity-preservation    = refl
  ; composition-preservation = λ f g → refl
  }

from-empty : { 𝓒 : Category } -> Functor empty-category 𝓒 
from-empty = record
  { object_map               = λ ()
  ; arrow_map                = λ {a} f → ⊥-elim a
  ; identity-preservation    = λ {a} -> ⊥-elim a
  ; composition-preservation = λ {a} -> λ f g → ⊥-elim a
  } 