module GroupBasics where
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Integer hiding (suc)
open import Data.Nat renaming (_+_ to _add_ ; _*_ to _ℕ*_)
open import Data.Integer.Properties

record Group : Set₁  where
  field
    type : Set
    ε : type
    _∙_ : type -> type -> type
    _⁻¹ : type -> type

    idL : (a : type) ->  a ∙ ε ≡ a
    idR : (a : type) ->  ε ∙ a ≡ a
    assoc : (a b c : type) -> (a ∙ b) ∙ c ≡ a ∙ (b ∙ c)
    inverseL : (a : type) -> a ∙ a ⁻¹ ≡ ε
    inverseR : (a : type) -> a ⁻¹ ∙ a ≡ ε

  infixl 50 _∙_
  infixl 90 _⁻¹

int-addition-group : Group
int-addition-group = record
  { type = ℤ
  ; ε = 0ℤ
  ; _∙_ = _+_
  ; _⁻¹ = λ x -> -1ℤ * x
  
  ; idL      = idL-lemma -- could just use +-identityʳ (looks like I got my L + R mixed up too)
  ; idR      = idR-lemma -- could just use +-identityˡ (looks like I got my L + R mixed up too)
  ; assoc    = +-assoc -- I looked at this but did not understand it very well
  ; inverseL = inverseL-lemma
  ; inverseR = inverseR-lemma
  }
  where 
    -- I bet there's a standard library proof for this...
    nat-id-lemma : {n : ℕ} -> n add 0 ≡ n
    nat-id-lemma {zero} = refl
    nat-id-lemma {suc n} = cong ℕ.suc (nat-id-lemma {n})

    idL-lemma : (a : ℤ) ->  a + 0ℤ ≡ a
    idL-lemma +0       = refl     -- zero
    idL-lemma +[1+ n ] = cong (λ u -> +[1+ u ]) nat-id-lemma
    idL-lemma -[1+ n ] = refl

    idR-lemma : (a : ℤ) -> 0ℤ + a ≡ a
    idR-lemma +0       = refl -- zero
    idR-lemma +[1+ n ] = refl -- positives
    idR-lemma -[1+ n ] = refl -- negatives

    inverseL-lemma : (a : ℤ) -> a + -1ℤ * a ≡ 0ℤ
    inverseL-lemma +0 = refl
    inverseL-lemma +[1+ n ]  = begin
      +[1+ n ] + -1ℤ * +[1+ n ] ≡⟨ refl ⟩
      suc n ⊖ suc (n add zero)  ≡⟨ cong (λ u -> suc n ⊖ suc u) (nat-id-lemma {n}) ⟩
      suc n ⊖ suc n             ≡⟨ n⊖n≡0 (suc n) ⟩
      0ℤ                        ∎
    inverseL-lemma -[1+ n ]  = begin
      -[1+ n ] + -1ℤ * -[1+ n ] ≡⟨ refl ⟩
      suc (n add zero) ⊖ suc n  ≡⟨ cong (λ u -> (suc u) ⊖ suc n) (nat-id-lemma {n})  ⟩
      suc n ⊖ suc n             ≡⟨ n⊖n≡0 (suc n) ⟩
      0ℤ                        ∎

    inverseR-lemma : (a : ℤ) → -1ℤ * a + a ≡ 0ℤ
    inverseR-lemma +0 = refl
    inverseR-lemma +[1+ n ] = begin
      -1ℤ * +[1+ n ] + +[1+ n ] ≡⟨ refl ⟩
      suc n ⊖ suc (n add zero)  ≡⟨ cong (λ u -> suc n ⊖ suc u) (nat-id-lemma {n}) ⟩
      suc n ⊖ suc n             ≡⟨ n⊖n≡0 (suc n) ⟩
      0ℤ                        ∎
    inverseR-lemma -[1+ n ] = begin
      -1ℤ * -[1+ n ] + -[1+ n ] ≡⟨ refl ⟩
      suc (n add zero) ⊖ suc n  ≡⟨ cong (λ u -> (suc u) ⊖ suc n) (nat-id-lemma {n})  ⟩
      suc n ⊖ suc n             ≡⟨ n⊖n≡0 (suc n) ⟩
      0ℤ                        ∎

