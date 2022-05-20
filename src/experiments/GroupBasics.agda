module GroupBasics where
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Integer hiding (suc)
open import Data.Nat renaming (_+_ to _add_ ; _*_ to _ℕ*_)

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
  
  ; idL = idL-lemma
  ; idR = idR-lemma
  ; assoc = assoc-lemma
  ; inverseL = {!   !}
  ; inverseR = {!   !}
  }
  where 
    idL-lemma : (a : ℤ) ->  a + 0ℤ ≡ a
    idL-lemma (+ 0)      = refl     -- zero
    idL-lemma (+[1+ n ]) = cong (λ u -> +[1+ u ]) nat-idL-lemma

      where
        -- I bet there's a standard library proof for this...
        nat-idL-lemma : {q : ℕ} -> q add 0 ≡ q
        nat-idL-lemma {zero} = refl
        nat-idL-lemma {ℕ.suc q} = cong ℕ.suc (nat-idL-lemma {q})
    idL-lemma (-[1+ n ]) = refl

    idR-lemma : (a : ℤ) -> 0ℤ + a ≡ a
    idR-lemma (+0)       = refl -- zero
    idR-lemma (+[1+ n ]) = refl -- positives
    idR-lemma (-[1+ n ]) = refl -- negatives

    assoc-lemma : (a b c : ℤ) -> (a + b) + c ≡ a + (b + c)
    assoc-lemma +0 b c = begin
      (0ℤ + b) + c ≡⟨ cong (λ u -> u + c) (idR-lemma b) ⟩
      b + c        ≡⟨ sym (idR-lemma (b + c)) ⟩
      0ℤ + (b + c) ∎    
    assoc-lemma a +0 c = begin
      (a + 0ℤ) + c ≡⟨ {!   !} ⟩
      a + c        ≡⟨ {!   !} ⟩
      a + (0ℤ + c) ∎  
    assoc-lemma a b +0 =    begin
      (a + b) + 0ℤ ≡⟨ idL-lemma (a + b) ⟩
      a + b        ≡⟨ cong (λ u -> a + u) (sym (idL-lemma b)) ⟩
      a + (b + 0ℤ) ∎  
    assoc-lemma +[1+ a ] +[1+ b ] +[1+ c ] = 
      begin
      +[1+ (a add suc b) add suc c ] ≡⟨ {!   !} ⟩
      +[1+ a add (suc b add suc c) ] ∎  
    assoc-lemma +[1+ a ] +[1+ b ] -[1+ c ] = {!   !}
    assoc-lemma +[1+ a ] -[1+ b ] +[1+ c ] = {!   !}
    assoc-lemma +[1+ a ] -[1+ b ] -[1+ c ] = {!   !}
    assoc-lemma -[1+ a ] +[1+ b ] +[1+ c ] = {!   !}
    assoc-lemma -[1+ a ] +[1+ b ] -[1+ c ] = {!   !}
    assoc-lemma -[1+ a ] -[1+ b ] +[1+ c ] = {!   !}
    assoc-lemma -[1+ a ] -[1+ b ] -[1+ c ] = 
      begin
      -[1+ suc (suc (a add b add c)) ] ≡⟨ {!   !} ⟩
      -[1+ suc (a add suc (b add c)) ] ∎  





