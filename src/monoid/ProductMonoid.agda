open import MonoidBasics
open import Data.Product
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning

module ProductMonoid (𝓜 𝓝 : Monoid) where

  open Monoid 𝓜 renaming (ε to φ ; _⊕_ to _⊙_ ; idL to idL-𝓜 ; idR to idR-𝓜 ; assoc to assoc-𝓜)
  open Monoid 𝓝 renaming (ε to ψ ; _⊕_ to _⊗_ ; idL to idL-𝓝 ; idR to idR-𝓝 ; assoc to assoc-𝓝)

  -- Extract the underlying set
  -- This is just a convenient operator syntax for `type`
  ⟦_⟧ : Monoid -> Set
  ⟦ 𝓞 ⟧ = Monoid.type 𝓞

  -- The type of product monoid elements
  ×-type : Set
  ×-type = ⟦ 𝓜 ⟧ × ⟦ 𝓝 ⟧

  -- The empty product monoid element
  ε : ×-type
  ε = φ , ψ

  -- Product monoid composition
  _⨂_ : ×-type -> ×-type -> ×-type
  (m₁ , n₁) ⨂ (m₂ , n₂) = (m₁ ⊙ m₂) , (n₁ ⊗ n₂)

  -- Your proofs go here!
  ×-idL : (a : ×-type) -> (a ⨂ (φ , ψ)) ≡ a 
  ×-idL (m , n) = 
    begin 
      (m , n) ⨂ (φ , ψ) 
        ≡⟨ refl ⟩ 
      (m ⊙ φ , n ⊗ ψ)
        ≡⟨ cong (λ u -> (u , n ⊗ ψ))  (idL-𝓜 m) ⟩
      (m , n ⊗ ψ)
        ≡⟨ cong (λ u -> (m , u))  (idL-𝓝 n) ⟩
      (m , n) 
    ∎ 
  ×-idR : (a : ×-type) -> ((φ , ψ) ⨂ a) ≡ a
  ×-idR (m , n) = 
    begin 
      (φ , ψ) ⨂ (m , n)
        ≡⟨ refl ⟩ 
      (φ ⊙ m , ψ ⊗ n)
        ≡⟨ cong (λ u -> (u , ψ ⊗ n))  (idR-𝓜 m) ⟩
      (m , ψ ⊗ n)
        ≡⟨ cong (λ u -> (m , u))  (idR-𝓝 n) ⟩
      (m , n) 
    ∎ 
  ×-assoc : (a b c : ×-type) -> (a ⨂ b) ⨂ c ≡ a ⨂ (b ⨂ c)
  ×-assoc (m₁ , n₁)(m₂ , n₂)(m₃ , n₃) = 
    begin 
      ((m₁ , n₁) ⨂ (m₂ , n₂)) ⨂ (m₃ , n₃)
        ≡⟨ refl ⟩ 
      (m₁ ⊙ m₂ , n₁ ⊗ n₂) ⨂ (m₃ , n₃)
        ≡⟨ refl ⟩ 
      (m₁ ⊙ m₂) ⊙ m₃ , (n₁ ⊗ n₂) ⊗ n₃
        ≡⟨ cong (λ u -> (u , (n₁ ⊗ n₂) ⊗ n₃)) (assoc-𝓜 m₁ m₂ m₃) ⟩ 
      m₁ ⊙ (m₂ ⊙ m₃) , (n₁ ⊗ n₂) ⊗ n₃
        ≡⟨ cong (λ u -> (m₁ ⊙ (m₂ ⊙ m₃) , u)) (assoc-𝓝 n₁ n₂ n₃) ⟩  
      m₁ ⊙ (m₂ ⊙ m₃) , n₁ ⊗ ( n₂ ⊗ n₃)
        ≡⟨ refl ⟩ 
      (m₁ , n₁) ⨂ (m₂ ⊙ m₃ , n₂ ⊗ n₃)  
        ≡⟨ refl ⟩ 
      (m₁ , n₁) ⨂ ((m₂ , n₂) ⨂ (m₃ , n₃)) 
    ∎ 

  -- Finally, let's build the monoid
  monoid : Monoid
  monoid = record
    { type  = ×-type
    ; ε     =  ε
    ; _⊕_   =  _⨂_
    ; idL   =  ×-idL
    ; idR   =  ×-idR
    ; assoc =  ×-assoc
    }