module MonoidBasics where

open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_^_)
open import Data.Bool
-- ≡
-- ∀

record Monoid : Set₁  where
    field
        type : Set
        -- dependant records below here, they depend on type
        ε : type
        _⊕_ : type -> type -> type

        idL :  (a : type) ->  a ⊕ ε ≡ a
        idR :  (a : type) ->  ε ⊕ a ≡ a
        assoc : (a b c : type) -> (a ⊕ b) ⊕ c ≡ a ⊕ (b ⊕ c)

    infixl 50 _⊕_
 
boolMonoid : Monoid
boolMonoid = record 
    { type = Bool 
    ; ε = true 
    ; _⊕_ = _∧_ -- and
    ; idL = λ { true -> refl ; false -> refl }
    ; idR = λ a -> refl 
    ; assoc = bool-assoc-lemma 
    }
    where
        bool-assoc-lemma : (a b c : Bool) -> (a ∧ b) ∧ c ≡ a ∧ b ∧ c
        bool-assoc-lemma false b c = refl -- because false && a == false
        bool-assoc-lemma true b c = refl  -- because true && a == a

module Properties (M : Monoid) where
    open Monoid M

    infix 60 _^_
    _^_ : type -> ℕ -> type
    a ^ 0 = ε
    a ^ (suc n) = a ⊕ (a ^ n)

    -- we have `ε ⊕ a ≡ a` and need to show `a ≡ ε ⊕ a`
    idR-reverse :  (a : type) ->  a ≡ ε ⊕ a
    idR-reverse a = sym (idR a) 
        
    expo-law-one : (x y : ℕ)(n : type) -> n ^ (x + y) ≡ n ^ x ⊕ n ^ y
    expo-law-one 0 0 n = idR-reverse ε
    expo-law-one 0 y n = idR-reverse (n ^ y)
    expo-law-one (suc x) y n = {!   !}

    -- cong (λ u -> n ⊕ u)  (expo-law-one (x y) (n))

    