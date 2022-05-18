module MonoidMorphisms where

open import MonoidBasics
open Monoid
open import Relation.Binary.PropositionalEquality

-- structure preserving map, i.e. f(x) . f(y) === f(x . y)
-- identity maps to identity map(e1) == e2
record MonoidMorphism (m n : Monoid) : Set where
    
    field
        map : type m -> type n
        idPreserve : map (ε m) ≡  ε n
        combPreserve : {a b : type m} -> map(_⊕_ m a b) ≡ (_⊕_ n (map a) (map b))
        
identityMorphism : (m : Monoid) -> MonoidMorphism m m
identityMorphism m = record { map = λ x -> x; idPreserve = refl ; combPreserve = refl }
    where open Monoid m 

open MonoidMorphism
open ≡-Reasoning

combineMorphism : {m n o : Monoid} -> MonoidMorphism m n -> MonoidMorphism n o -> MonoidMorphism m o
combineMorphism {m} {n} {o} f g = record { 
    map = λ x → map g (map f x) ; 
    idPreserve = begin 
            mapG (mapF εM) 
              ≡⟨ cong mapG idPreserveF ⟩ 
            mapG εN 
              ≡⟨ idPreserveG ⟩ 
            εO 
        ∎ ; 
    combPreserve = λ {a} {b} → begin 
            mapG (mapF (a ⊕m b)) 
              ≡⟨ cong mapG combPreserveF ⟩ 
            mapG (mapF a ⊕n mapF b) 
              ≡⟨ combPreserveG ⟩ 
            (mapG (mapF a) ⊕o mapG (mapF b)) 
        ∎ }
    where 
        open Monoid m renaming (ε to εM ; _⊕_ to _⊕m_)
        open Monoid n renaming (ε to εN ; _⊕_ to _⊕n_)
        open Monoid o renaming (ε to εO ; _⊕_ to _⊕o_)
        open MonoidMorphism f renaming (map to mapF ; idPreserve to idPreserveF ; combPreserve to combPreserveF)
        open MonoidMorphism g renaming (map to mapG ; idPreserve to idPreserveG ; combPreserve to combPreserveG)

-- (x y : A)
-- (p q : x ≡ y)
-- p ≡ q

product : Monoid -> Monoid -> Monoid
product M N = ?

-- unit
terminalMonoid : Monoid 
terminalMonoid = ?

morphismToTerminal : (m : Monoid) -> MonoidMorphism m terminalMonoid
morphismToTerminal m = ?

-- 4 -> 2
-- {1, -1, i, -i} squared -> {1, -1}

