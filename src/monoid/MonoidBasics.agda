module MonoidBasics where

open import Relation.Binary.PropositionalEquality
open import Data.Nat hiding (_^_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Nat.Properties

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
        bool-assoc-lemma : (a b c : Bool) -> (a ∧ b) ∧ c ≡ a ∧ (b ∧ c)
        bool-assoc-lemma false b c = refl -- because false && a == false
        bool-assoc-lemma true b c = refl  -- because true && a == a

intMonoid : Monoid
intMonoid = record 
    { type = ℕ 
    ; ε = 0 
    ; _⊕_ = _+_ 
    ; idL = int-idL-lemma
    ; idR = λ a -> refl 
    ; assoc = int-assoc-lemma 
    }
    where
        int-assoc-lemma : (a b c : ℕ) -> (a + b) + c ≡ a + (b + c)
        int-assoc-lemma 0 b c = refl
        -- need to show ((suc a) + b) + c === (suc a) + (b + c)
        -- since I use refl in the below except for one step this can be written as simply
        -- int-assoc-lemma (suc a) b c = cong suc (int-assoc-lemma a b c)
        -- but I think for now it's nice to show the intermediaries, makes it easier for a human to follow
        int-assoc-lemma (suc a) b c = begin
          ((suc a) + b) + c ≡⟨ refl ⟩
          suc (a + b) + c   ≡⟨ refl ⟩
          suc (a + b + c)   ≡⟨ refl ⟩
          suc ((a + b) + c) ≡⟨ cong suc (int-assoc-lemma a b c) ⟩
          suc (a + (b + c)) ≡⟨ refl ⟩
          (suc a) + (b + c) ∎
        int-idL-lemma : (a : ℕ) -> a + 0 ≡ a
        int-idL-lemma zero = refl
        int-idL-lemma (suc x) = cong suc (int-idL-lemma x)
        
module Properties (M : Monoid) where
    open Monoid M

    infix 60 _^_
    _^_ : type -> ℕ -> type
    a ^ 0 = ε
    a ^ (suc n) = a ⊕ (a ^ n)

    -- we have `ε ⊕ a ≡ a` and need to show `a ≡ ε ⊕ a`
    idR-reverse :  (a : type) ->  a ≡ ε ⊕ a
    idR-reverse a = sym (idR a) 

    expo-law-power-of-1 : (a : type) -> a ^ 1 ≡ a
    expo-law-power-of-1 = idL 

    expo-law-zero : (x : ℕ) -> ε ≡ ε ^ x
    expo-law-zero 0 = refl
    expo-law-zero (suc x) = 
      begin
        ε
          ≡⟨ idR-reverse ε ⟩
        ε ⊕ ε
          ≡⟨ cong (λ u -> ε ⊕ u) (expo-law-zero x) ⟩
        ε ⊕ (ε ^ x)
          ≡⟨ refl ⟩ -- a ^ (suc n) = a ⊕ (a ^ n) is the definition remmeber
        ε ^ (suc x)
      ∎
            
    expo-law-one : (x y : ℕ)(n : type) -> n ^ (x + y) ≡ n ^ x ⊕ n ^ y
    expo-law-one 0 0 n = idR-reverse ε
    expo-law-one 0 y n = idR-reverse (n ^ y)
    -- need to show `n ⊕ n ^ (x + y) ≡ n ⊕ n ^ x ⊕ n ^ y` in the below
    expo-law-one (suc x) y n = 
      begin
        (n ⊕ n ^ (x + y))
          ≡⟨ cong (λ u -> n ⊕ u) (expo-law-one x y n) ⟩
        (n ⊕ (n ^ x ⊕ n ^ y))
          ≡⟨ sym (assoc (n) (n ^ x) (n ^ y)) ⟩
        (n ⊕ n ^ x ⊕ n ^ y)
      ∎

    mult-zero-law : (n : ℕ) -> n * 0 ≡ 0
    mult-zero-law 0 = refl
    mult-zero-law (suc n) = mult-zero-law n

    expo-law-two : (x y : ℕ)(n : type) -> n ^ (x * y) ≡ (n ^ y) ^ x
    -- don't actually need `expo-law-two 0 0 n` base case but I thought it would be interesting to show
    expo-law-two 0 0 n = refl
    expo-law-two 0 y n = refl
    -- don't actually need `expo-law-two x 0 n` base case but I thought it would be interesting to show
    expo-law-two x 0 n =
      begin
        n ^ (x * 0)
          ≡⟨ cong (λ (u : ℕ) -> n ^ u) ( mult-zero-law x) ⟩
        n ^ 0
          ≡⟨ refl ⟩
        ε
          ≡⟨ expo-law-zero x ⟩
        ε ^ x
      ∎ 
    expo-law-two (suc x) y n = 
      begin
        n ^ (suc x * y)
          ≡⟨ refl ⟩
        n ^ ((1 + x) * y)
          ≡⟨ refl ⟩
        n ^ (y + x * y)
          ≡⟨ expo-law-one y (x * y) n ⟩
        n ^ y ⊕ n ^ (x * y)
          ≡⟨ cong (λ u -> n ^ y ⊕ u) (expo-law-two x y n) ⟩
        (n ^ y) ⊕ (n ^ y) ^ x
          ≡⟨ refl ⟩ 
          -- I don't know how agda knows these are equivalent!!! 
          -- I personally can see they're equivalent by using (n ^ y) === (n ^ y) ^ 1 and expo-law-one
          -- I think under the hood it MUST be using the definition `a ^ (suc n) = a ⊕ (a ^ n)` but in reverse
          -- Perhaps a law we can show is a === a ^ 1
        (n ^ y) ^ (1 + x)
          ≡⟨ refl ⟩
        (n ^ y) ^ suc x
      ∎ 
      