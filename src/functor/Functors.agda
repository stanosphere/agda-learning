module functor.Functors where

open import CategoryBasics
open Category hiding (_โ_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open โก-Reasoning
open import Data.Unit
open import Data.Empty
open import Function.Base hiding (id)


record Functor (๐ ๐ : Category) : Set where
  field
    object-map : (X : object ๐) -> object ๐
    arrow-map : โ { a b : object ๐ } -> ( f : arrow ๐ a b ) -> arrow ๐ (object-map a) (object-map b)

    -- laws
    -- for all a in ๐ arrow-mapping id gets mapped to id on object-map of a
    identity-preservation : โ { a : object ๐ } -> arrow-map (id ๐ a) โก id ๐ (object-map a)
    -- for all objects in C, composing and then mapping is identical to mapping first and then composing
    composition-preservation :
      โ { a b c : object ๐ } -> 
      (f : arrow ๐ b c) (g : arrow ๐ a b) -> 
      arrow-map (compose ๐ f g) โก compose ๐ (arrow-map f) (arrow-map g)
    
-- comparison with scala Functor
-- map : (A -> B) -> List[A] -> List[B]
-- object-map: List: Type -> Type, C = Scala type, D = Scala type
-- arrow-map: (A -> B) -> (List[A] -> List[B])

-- map(f compose g) === (map f) compose (map g)
-- map(x -> x) === identity

functor-composition : { ๐ ๐ ๐ : Category } -> (๐ : Functor ๐ ๐) -> (๐ : Functor ๐ ๐) -> Functor ๐ ๐
functor-composition { A } { B } { C } F G = record
  { object-map = object-map'
  ; arrow-map =  arrow-map'
  ; identity-preservation = identity-preservation'
  ; composition-preservation = composition-preservation'
  }
    where 
      open Functor F
      open Functor G
      object-map' = object-map F โ object-map G

      arrow-map' : โ { a b : object A } -> ( f : arrow A a b ) -> arrow C (object-map' a) (object-map' b)
      arrow-map' = arrow-map F โ arrow-map G

      identity-preservation' : {a : object A} โ arrow-map' (id A a) โก id C (object-map' a)
      identity-preservation' { a } = begin
        arrow-map' (id A a)                  โกโจ refl โฉ
        (arrow-map F โ arrow-map G) (id A a) โกโจ cong (arrow-map F) (identity-preservation G) โฉ
        arrow-map F (id B (object-map G a))  โกโจ identity-preservation F โฉ
        id C (object-map F (object-map G a)) โกโจ refl โฉ
        id C (object-map' a)                 โ 

      composition-preservation' : {a b c : object A} (f : arrow A b c) (g : arrow A a b) โ arrow-map' (compose A f g) โก compose C (arrow-map' f) (arrow-map' g)
      composition-preservation' {a} {b} {c} f g = begin 
        arrow-map' (compose A f g)                                            โกโจ refl โฉ
        (arrow-map F โ arrow-map G) (compose A f g)                           โกโจ cong (arrow-map F) (composition-preservation G f g) โฉ
        arrow-map F (compose B (arrow-map G f) (arrow-map G g))               โกโจ composition-preservation F (arrow-map G f) (arrow-map G g) โฉ
        compose C (arrow-map F (arrow-map G f)) (arrow-map F (arrow-map G g)) โกโจ refl โฉ
        compose C (arrow-map' f) (arrow-map' g)                               โ

id-functor : { ๐ : Category } -> Functor ๐ ๐
id-functor = record
  { object-map = ฮป X -> X
  ; arrow-map = ฮป f -> f
  ; identity-preservation = refl
  ; composition-preservation = ฮป f g -> refl
  } 

to-singleton : { ๐ : Category } -> Functor ๐ singleton-category
to-singleton = record
  { object-map               = ฮป X -> tt
  ; arrow-map                = ฮป f -> tt
  ; identity-preservation    = refl
  ; composition-preservation = ฮป f g -> refl
  }

from-empty : { ๐ : Category } -> Functor empty-category ๐ 
from-empty = record
  { object-map               = ฮป ()
  ; arrow-map                = ฮป {a} f -> โฅ-elim a
  ; identity-preservation    = ฮป {a} -> โฅ-elim a
  ; composition-preservation = ฮป {a} -> ฮป f g -> โฅ-elim a
  } 

variable
  A B C : Set 

postulate
  -- pointwise equality => eqaulity
  funex : {f g : A -> B} -> ((a : A) -> f a โก g a) -> f โก g

MAYBE : Functor SET SET
MAYBE = record
  { object-map = Maybe
  ; arrow-map = ฮป f x -> map f x
  ; identity-preservation = funex identity-preservation' 
  ; composition-preservation = ฮป f g -> funex (composition-preservation' f g)
  }
    where
      open import Data.Maybe
      identity-preservation' : (a : Maybe A) -> map (ฮป x -> x) a โก a
      identity-preservation' (just x) = refl
      identity-preservation' nothing = refl

      composition-preservation' : (f : B -> C)(g : A -> B)(a : Maybe A) -> map (f โ g) a โก (map f โ map g) a
      composition-preservation' f g (just x) = refl
      composition-preservation' f g nothing = refl

LIST : Functor SET SET
LIST = record
  { object-map = List
  ; arrow-map = ฮป f x -> map f x
  ; identity-preservation = funex identity-preservation'
  ; composition-preservation = ฮป f g -> funex (composition-preservation' f g)
  }
    where 
      open import Data.List
      identity-preservation' : (xs : List A) -> map (ฮป x -> x) xs โก xs
      identity-preservation' [] = refl
      identity-preservation' (x โท xs) = cong (ฮป u -> [ x ] ++ u) (identity-preservation' xs)

      composition-preservation' : (f : B -> C)(g : A -> B)(a : List A) -> map (f โ g) a โก (map f โ map g) a
      composition-preservation' f g [] = refl
      composition-preservation' f g (x โท xs) = cong (ฮป u -> [ (f โ g) x ] ++ u) (composition-preservation' f g xs)

Reader : Set -> Set -> Set
Reader E A = E -> A

READER : (E : Set) -> Functor SET SET
READER E = record
  { object-map = Reader E
  ; arrow-map = ฮป f g e -> f (g e)
  ; identity-preservation = refl
  ; composition-preservation = ฮป f g -> refl
  }

open import Data.Product

Writer : Set -> Set -> Set
Writer E A = A ร E

WRITER : (E : Set) -> Functor SET SET
WRITER E = record
  { object-map = Writer E
  ; arrow-map = ฮป f โ ฮป { (a , b) โ f a , b }
  ; identity-preservation = refl
  ; composition-preservation = ฮป f g โ refl
  }
