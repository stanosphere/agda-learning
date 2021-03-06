open import monoid.MonoidBasics
open import Data.Product
open import Relation.Binary.PropositionalEquality
open โก-Reasoning

module monoid.ProductMonoid (๐ ๐ : Monoid) where

  open Monoid ๐ renaming (ฮต to ฯ ; _โ_ to _โ_ ; idL to idL-๐ ; idR to idR-๐ ; assoc to assoc-๐)
  open Monoid ๐ renaming (ฮต to ฯ ; _โ_ to _โ_ ; idL to idL-๐ ; idR to idR-๐ ; assoc to assoc-๐)

  -- Extract the underlying set
  -- This is just a convenient operator syntax for `type`
  โฆ_โง : Monoid -> Set
  โฆ ๐ โง = Monoid.type ๐

  -- The type of product monoid elements
  ร-type : Set
  ร-type = โฆ ๐ โง ร โฆ ๐ โง

  -- The empty product monoid element
  ฮต : ร-type
  ฮต = ฯ , ฯ

  -- Product monoid composition
  _โจ_ : ร-type -> ร-type -> ร-type
  (mโ , nโ) โจ (mโ , nโ) = (mโ โ mโ) , (nโ โ nโ)

  -- Your proofs go here!
  ร-idL : (a : ร-type) -> (a โจ (ฯ , ฯ)) โก a 
  ร-idL (m , n) = 
    begin 
      (m , n) โจ (ฯ , ฯ) 
        โกโจ refl โฉ 
      (m โ ฯ , n โ ฯ)
        โกโจ cong (ฮป u -> (u , n โ ฯ))  (idL-๐ m) โฉ
      (m , n โ ฯ)
        โกโจ cong (ฮป u -> (m , u))  (idL-๐ n) โฉ
      (m , n) 
    โ 
  ร-idR : (a : ร-type) -> ((ฯ , ฯ) โจ a) โก a
  ร-idR (m , n) = 
    begin 
      (ฯ , ฯ) โจ (m , n)
        โกโจ refl โฉ 
      (ฯ โ m , ฯ โ n)
        โกโจ cong (ฮป u -> (u , ฯ โ n))  (idR-๐ m) โฉ
      (m , ฯ โ n)
        โกโจ cong (ฮป u -> (m , u))  (idR-๐ n) โฉ
      (m , n) 
    โ 
  ร-assoc : (a b c : ร-type) -> (a โจ b) โจ c โก a โจ (b โจ c)
  ร-assoc (mโ , nโ)(mโ , nโ)(mโ , nโ) = 
    begin 
      ((mโ , nโ) โจ (mโ , nโ)) โจ (mโ , nโ)
        โกโจ refl โฉ 
      (mโ โ mโ , nโ โ nโ) โจ (mโ , nโ)
        โกโจ refl โฉ 
      (mโ โ mโ) โ mโ , (nโ โ nโ) โ nโ
        โกโจ cong (ฮป u -> (u , (nโ โ nโ) โ nโ)) (assoc-๐ mโ mโ mโ) โฉ 
      mโ โ (mโ โ mโ) , (nโ โ nโ) โ nโ
        โกโจ cong (ฮป u -> (mโ โ (mโ โ mโ) , u)) (assoc-๐ nโ nโ nโ) โฉ  
      mโ โ (mโ โ mโ) , nโ โ ( nโ โ nโ)
        โกโจ refl โฉ 
      (mโ , nโ) โจ (mโ โ mโ , nโ โ nโ)  
        โกโจ refl โฉ 
      (mโ , nโ) โจ ((mโ , nโ) โจ (mโ , nโ)) 
    โ 

  -- Finally, let's build the monoid
  monoid : Monoid
  monoid = record
    { type  = ร-type
    ; ฮต     =  ฮต
    ; _โ_   =  _โจ_
    ; idL   =  ร-idL
    ; idR   =  ร-idR
    ; assoc =  ร-assoc
    }