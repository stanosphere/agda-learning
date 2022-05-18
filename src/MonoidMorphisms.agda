module MonoidMorphisms where

open import MonoidBasics
open Monoid
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Unit
open import Data.Product hiding (map)
open import Data.Bool

-- structure preserving map, i.e. f(x) . f(y) === f(x . y)
-- identity maps to identity f(e1) == e2
record MonoidMorphism (m n : Monoid) : Set where
  field
    map : type m -> type n
    idPreserve : map (ε m) ≡  ε n
    combPreserve : {a b : type m} -> map(_⊕_ m a b) ≡ (_⊕_ n (map a) (map b))
        
identityMorphism : (m : Monoid) -> MonoidMorphism m m
identityMorphism m = record 
  { map = λ x -> x
  ; idPreserve = refl 
  ; combPreserve = refl 
  }
    where open Monoid m 

open MonoidMorphism
open ≡-Reasoning

-- composing the mapping function for any pair of morphisms guarentees we produce another morphism
combineMorphism : {m n o : Monoid} -> MonoidMorphism m n -> MonoidMorphism n o -> MonoidMorphism m o
combineMorphism {m} {n} {o} f g = record 
  { map = λ x → map g (map f x) 
  ; idPreserve = 
    begin 
      mapG (mapF εM) 
        ≡⟨ cong mapG idPreserveF ⟩ 
      mapG εN 
        ≡⟨ idPreserveG ⟩ 
      εO 
    ∎ 
  ; combPreserve = 
    λ {a} {b} -> begin 
      mapG (mapF (a ⊕m b)) 
        ≡⟨ cong mapG combPreserveF ⟩ 
      mapG (mapF a ⊕n mapF b) 
        ≡⟨ combPreserveG ⟩ 
      (mapG (mapF a) ⊕o mapG (mapF b)) 
    ∎ 
  }
    where 
      open Monoid m renaming (ε to εM ; _⊕_ to _⊕m_)
      open Monoid n renaming (ε to εN ; _⊕_ to _⊕n_)
      open Monoid o renaming (ε to εO ; _⊕_ to _⊕o_)
      open MonoidMorphism f renaming (map to mapF ; idPreserve to idPreserveF ; combPreserve to combPreserveF)
      open MonoidMorphism g renaming (map to mapG ; idPreserve to idPreserveG ; combPreserve to combPreserveG)

-- given a pair of proofs that a pair of values are equal agda can show that the proof must be equal
-- (x y : A)
-- (p q : x ≡ y)
-- p ≡ q

product : Monoid -> Monoid -> Monoid
product M N = record
  { type  =  (type M) × (type N)
  ; ε     = ε M , ε N 
  ; _⊕_   = _|+|_
  ; idL   = idL-product-lemma 
  ; idR   =  idR-product-lemma
  ; assoc = assoc-product-lemma
  }
    where 
      open Monoid M renaming (ε to εM ; _⊕_ to _⊕m_ ; type to typeM)
      open Monoid N renaming (ε to εN ; _⊕_ to _⊕n_ ; type to typeN)
      _|+|_ : (type M) × (type N) -> (type M) × (type N) -> (type M) × (type N)
      _|+|_ (m1 , n1) (m2 , n2) = (m1 ⊕m m2) , (n1 ⊕n n2)
      idL-product-lemma : (x : (type M) × (type N)) ->  x |+| (ε M , ε N) ≡ x 
      idL-product-lemma (m , n) = {!   !}
      idR-product-lemma : (x : (type M) × (type N)) -> (ε M , ε N) |+| x ≡ x 
      idR-product-lemma (m , n) = {!   !}
      assoc-product-lemma : (x y z : (type M) × (type N)) -> (x |+| y) |+| z ≡ x |+| (y |+| z)
      assoc-product-lemma (mx , nx) (my , ny) (mz , nz) = {!   !}
      
-- unit monoid containing a single element
terminalMonoid : Monoid 
terminalMonoid = record
  { type = ⊤ 
  ; ε =  tt
  ; _⊕_ = λ a b -> tt 
  ; idL = λ a -> refl 
  ; idR = λ a -> refl 
  ; assoc = λ a b c -> refl 
  }

-- for any monoid we can always produce a morphism that takes it to the terminalMonoid
morphismToTerminal : (m : Monoid) -> MonoidMorphism m terminalMonoid
morphismToTerminal m = record 
  { map = λ a -> tt
  ; idPreserve = refl 
  ; combPreserve = refl 
  }

-- 4 -> 2
-- {1, -1, i, -i} squared -> {1, -1}
