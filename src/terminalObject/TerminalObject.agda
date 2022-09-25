{-# OPTIONS --type-in-type #-}

module terminalObject.TerminalObject where

open import CategoryBasics
open import Relation.Binary.PropositionalEquality
open import Data.Unit
open import Data.Nat
open import functor.Functors
open import Leq

record Terminal {𝓒 : Category} : Set where
  open Category 𝓒

  field
    terminal : object

    to     : (Y : object) -> arrow Y terminal
    unique :  {Y : object} -> ( other : arrow Y terminal ) -> other ≡ to Y


SET-terminal : Terminal {SET}
SET-terminal = record
  { terminal = ⊤
  ; to = λ Y x → tt
  ; unique = λ other → funex (λ a → refl )
  }

GEQ : Category
GEQ = opposite-category LEQ

GEQ-terminal : Terminal {GEQ}
GEQ-terminal = record
  { terminal = 0
  ; to = λ Y → z≤n
  ; unique = λ { z≤n -> refl }
  }