module MonoidMorphisms where

open import MonoidBasics
open Monoid
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Unit
open import Data.Product hiding (map)
open import Data.Bool

-- structure preserving map, i.e. f(x) . f(y) === f(x . y)
-- identity maps to identity f(e1) == e2
record MonoidMorphism (𝓜 𝓝 : Monoid) : Set where
  open Monoid 𝓜 renaming (ε to φ ; _⊕_ to _⊙_)
  open Monoid 𝓝 renaming (ε to ψ ; _⊕_ to _⊗_)
  ⟦_⟧ : Monoid -> Set
  ⟦ 𝓞 ⟧ = Monoid.type 𝓞
  field
    map          : ⟦ 𝓜 ⟧ -> ⟦ 𝓝 ⟧
    idPreserve   : map φ ≡ ψ
    combPreserve : {a b : ⟦ 𝓜 ⟧} -> map(a ⊙ b) ≡ (map a) ⊗ (map b)
        
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
  ; idPreserve = begin 
      mapG (mapF εM) ≡⟨ cong mapG idPreserveF ⟩ 
      mapG εN        ≡⟨ idPreserveG ⟩ 
      εO             ∎ 
  ; combPreserve = 
    λ {a} {b} -> begin 
      mapG (mapF (a ⊕m b))           ≡⟨ cong mapG combPreserveF ⟩ 
      mapG (mapF a ⊕n mapF b)        ≡⟨ combPreserveG ⟩ 
      mapG (mapF a) ⊕o mapG (mapF b) ∎ 
  }
    where 
      open Monoid m renaming (ε to εM ; _⊕_ to _⊕m_)
      open Monoid n renaming (ε to εN ; _⊕_ to _⊕n_)
      open Monoid o renaming (ε to εO ; _⊕_ to _⊕o_)
      open MonoidMorphism f renaming (map to mapF ; idPreserve to idPreserveF ; combPreserve to combPreserveF)
      open MonoidMorphism g renaming (map to mapG ; idPreserve to idPreserveG ; combPreserve to combPreserveG)

-- unit monoid containing a single element
terminalMonoid : Monoid 
terminalMonoid = record
  { type  = ⊤ 
  ; ε     = tt
  ; _⊕_   = λ a b -> tt 
  ; idL   = λ a -> refl 
  ; idR   = λ a -> refl 
  ; assoc = λ a b c -> refl 
  }

-- for any monoid we can always produce a morphism that takes it to the terminalMonoid
morphismToTerminal : (m : Monoid) -> MonoidMorphism m terminalMonoid
morphismToTerminal m = record 
  { map          = λ a -> tt
  ; idPreserve   = refl 
  ; combPreserve = refl 
  }

-- potentially interesting morphism to try to encode
-- 4 -> 2
-- {1, -1, i, -i} squared -> {1, -1}

-- random agda fact
-- given a pair of proofs that a pair of values are equal agda can show that the proof must be equal
-- (x y : A)
-- (p q : x ≡ y)
-- p ≡ q

module MonoidMorphismInstances where
  ∧-to-∨-monoid-morphism : MonoidMorphism bool-monoid-∧ bool-monoid-∨
  ∧-to-∨-monoid-morphism = record 
    { map          = not 
    ; idPreserve   = refl 
    ; combPreserve = λ {a b} -> comb-preserve-lemma a b
    }
      where
        comb-preserve-lemma : (a b : Bool) -> not(a ∧ b) ≡ (not a) ∨ (not b)
        comb-preserve-lemma false y = refl
        comb-preserve-lemma true y  = refl

  ∨-to-∧-monoid-morphism : MonoidMorphism bool-monoid-∨ bool-monoid-∧
  ∨-to-∧-monoid-morphism = record 
    { map          = not 
    ; idPreserve   = refl 
    ; combPreserve = λ {a b} -> comb-preserve-lemma a b
    }
      where
        comb-preserve-lemma : (a b : Bool) -> not (a ∨ b) ≡ not a ∧ not b
        comb-preserve-lemma false y = refl
        comb-preserve-lemma true y  = refl
  
  