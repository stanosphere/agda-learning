module functor.Functors where

open import CategoryBasics
open Category hiding (_∘_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Data.Unit
open import Data.Empty
open import Function.Base hiding (id)


record Functor (𝓒 𝓓 : Category) : Set where
  field
    object-map : (X : object 𝓒) -> object 𝓓
    arrow-map : ∀ { a b : object 𝓒 } -> ( f : arrow 𝓒 a b ) -> arrow 𝓓 (object-map a) (object-map b)

    -- laws
    -- for all a in 𝓒 arrow-mapping id gets mapped to id on object-map of a
    identity-preservation : ∀ { a : object 𝓒 } -> arrow-map (id 𝓒 a) ≡ id 𝓓 (object-map a)
    -- for all objects in C, composing and then mapping is identical to mapping first and then composing
    composition-preservation :
      ∀ { a b c : object 𝓒 } -> 
      (f : arrow 𝓒 b c) (g : arrow 𝓒 a b) -> 
      arrow-map (compose 𝓒 f g) ≡ compose 𝓓 ( arrow-map f ) (arrow-map g)
    
-- comparison with scala Functor
-- map : (A -> B) -> List[A] -> List[B]
-- object-map: List: Type -> Type, C = Scala type, D = Scala type
-- arrow-map: (A -> B) -> (List[A] -> List[B])

-- map(f compose g) === (map f) compose (map g)
-- map(x -> x) === identity

id-functor : { 𝓒 : Category } -> Functor 𝓒 𝓒
id-functor = record
  { object-map = λ X -> X
  ; arrow-map = λ f -> f
  ; identity-preservation = refl
  ; composition-preservation = λ f g -> refl
  } 

to-singleton : { 𝓒 : Category } -> Functor 𝓒 singleton-category
to-singleton = record
  { object-map               = λ X -> tt
  ; arrow-map                = λ f -> tt
  ; identity-preservation    = refl
  ; composition-preservation = λ f g -> refl
  }

from-empty : { 𝓒 : Category } -> Functor empty-category 𝓒 
from-empty = record
  { object-map               = λ ()
  ; arrow-map                = λ {a} f -> ⊥-elim a
  ; identity-preservation    = λ {a} -> ⊥-elim a
  ; composition-preservation = λ {a} -> λ f g -> ⊥-elim a
  } 

variable
  A B C : Set 

postulate
  -- pointwise equality => eqaulity
  funex : {f g : A -> B} -> ((a : A) -> f a ≡ g a) -> f ≡ g

MAYBE : Functor SET SET
MAYBE = record
  { object-map = Maybe
  ; arrow-map = λ f x -> map f x
  ; identity-preservation = funex identity-preservation' 
  ; composition-preservation = λ f g -> funex (composition-preservation' f g)
  }
    where
      open import Data.Maybe
      identity-preservation' : (a : Maybe A) -> map (λ x -> x) a ≡ a
      identity-preservation' (just x) = refl
      identity-preservation' nothing = refl

      composition-preservation' : (f : B -> C)(g : A -> B)(a : Maybe A) -> map (f ∘ g) a ≡ (map f ∘ map g) a
      composition-preservation' f g (just x) = refl
      composition-preservation' f g nothing = refl

LIST : Functor SET SET
LIST = record
  { object-map = List
  ; arrow-map = λ f x -> map f x
  ; identity-preservation = funex identity-preservation'
  ; composition-preservation = λ f g -> funex (composition-preservation' f g)
  }
    where 
      open import Data.List
      identity-preservation' : (xs : List A) -> map (λ x -> x) xs ≡ xs
      identity-preservation' [] = refl
      identity-preservation' (x ∷ xs) = cong (λ u -> [ x ] ++ u) (identity-preservation' xs)

      composition-preservation' : (f : B -> C)(g : A -> B)(a : List A) -> map (f ∘ g) a ≡ (map f ∘ map g) a
      composition-preservation' f g [] = refl
      composition-preservation' f g (x ∷ xs) = cong (λ u -> [ (f ∘ g) x ] ++ u) (composition-preservation' f g xs)

Reader : Set -> Set -> Set
Reader E A = E -> A

READER : (E : Set) -> Functor SET SET
READER E = record
  { object-map = Reader E
  ; arrow-map = λ f g e -> f (g e)
  ; identity-preservation = refl
  ; composition-preservation = λ f g -> refl
  }

open import Data.Product

Writer : Set -> Set -> Set
Writer E A = A × E

WRITER : (E : Set) -> Functor SET SET
WRITER E = record
  { object-map = Writer E
  ; arrow-map = λ f → λ { (a , b) → f a , b }
  ; identity-preservation = refl
  ; composition-preservation = λ f g → refl
  }
