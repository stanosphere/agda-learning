module monoid.MonoidMorphisms where

open import monoid.MonoidBasics
open Monoid
open import Relation.Binary.PropositionalEquality
open import Agda.Builtin.Unit
open import Data.Product hiding (map)
open import Data.Bool
open import Function.Base hiding (id)

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
        
identity-morphism : (m : Monoid) -> MonoidMorphism m m
identity-morphism m = record 
  { map = λ x -> x
  ; idPreserve = refl 
  ; combPreserve = refl 
  }
    where open Monoid m 

open MonoidMorphism
open ≡-Reasoning

-- composing the mapping function for any pair of morphisms guarentees we produce another morphism
combine-morphism : {m n o : Monoid} -> MonoidMorphism n o -> MonoidMorphism m n ->  MonoidMorphism m o
combine-morphism {m} {n} {o} f g = record 
  { map = map f ∘ map g 
  ; idPreserve = begin 
      (mapF ∘ mapG) εM ≡⟨ cong mapF idPreserveG ⟩ 
      mapF εN          ≡⟨ idPreserveF ⟩ 
      εO               ∎ 
  ; combPreserve = 
    λ {a} {b} -> begin 
      (mapF ∘ mapG) (a ⊕m b)                  ≡⟨ cong mapF combPreserveG ⟩ 
      mapF (mapG a ⊕n mapG b)                 ≡⟨ combPreserveF ⟩ 
      (mapF ∘  mapG $ a) ⊕o (mapF ∘ mapG $ b) ∎ 
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
  
  