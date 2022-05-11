module Finite where

open import Data.Nat
open import Data.Empty
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality

variable
  n m : ℕ
  A : Set

infixr 30 _∷_

-- We could define Finite sets as a function ...
-- But it turns out that they're quite hard to use this way
-- and data is a little better
module Fin' where
  Fin' : ℕ -> Set
  Fin' 0             = ⊥
  Fin' 1             = ⊤
  Fin' (suc (suc n)) = ⊤ × Fin' (suc n)

-- 0 is empty
-- 1 has one element
-- n + 1 has all the elements of n and one more
data Fin : ℕ -> Set where
  fz : ∀ {n} -> Fin (suc n)
  fs : ∀ {n} -> Fin n -> Fin (suc n)

-- Some "evidence"
f0 : ¬ Fin 0
f0 ()

f1 : Fin 1
f1 = fz

f2 : Fin 2
f2 = fz

f2' : Fin 2
f2' = fs fz

f1-unique : ∀ (f g : Fin 1) -> f ≡ g
f1-unique fz fz = refl

-- Vectors of a fixed length
data Vec (A : Set) : ℕ -> Set where
  [] : Vec A 0
  _∷_ : (a : A) -> Vec A n -> Vec A (suc n)

-- We can use finite sets to index vectors
_!_ : Vec A n -> Fin n -> A
(a ∷ v) ! fz   = a
(a ∷ v) ! fs x = v ! x

-- NxM matraces are just vectors of vectors
Matrix : (A : Set) -> (n m : ℕ) -> Set
Matrix A n m = Vec (Vec A n) m

ex1 : Matrix ℕ 2 3
ex1 = (1 ∷ 2 ∷ [])
    ∷ (3 ∷ 4 ∷ [])
    ∷ (5 ∷ 6 ∷ [])
    ∷ []

-- We can represent coordinates in a few ways,
-- Firstly via a direct data definition
module Coords where
  data Coord : ℕ -> ℕ -> Set where
    row : ∀ {n m} -> Fin n     -> Coord n (suc m)
    col : ∀ {n m} -> Coord n m -> Coord n (suc m)

  _!!_ : Matrix A n m -> Coord n m -> A
  (r ∷ s) !! row x = r ! x
  (r ∷ s) !! col v = s !! v

-- But perhaps using product types here is actually more intuitive
Coord : (n m : ℕ) -> Set
Coord n m = Fin n × Fin m

_!!_ : Matrix A n m -> Coord n m -> A
(r ∷ s) !! (x , fz)   = r ! x
(r ∷ s) !! (x , fs y) = s !! (x , y)

-- Perfectly balanced binary trees of depth n
data Tree (A : Set): ℕ -> Set where
  leaf   : (a : A) -> Tree A 1
  branch : ∀ {n} -> (a : A) -> Tree A n -> Tree A n -> Tree A (suc n)

-- ... can be indexed by paths through those trees
-- We can reach the end of a path
-- We can turn left and continue with another path
-- Or we can turn right and continue with another path
data Path : ℕ -> Set where
  end   : Path (suc n)
  left  : Path n -> Path (suc n)
  right : Path n -> Path (suc n)

_!!!_ : ∀ {n} -> Tree A n -> Path n -> A
leaf a       !!! end     = a
branch a l r !!! end     = a
branch a l r !!! left  p = l !!! p
branch a l r !!! right p = r !!! p

-- Some lemmas about how ×, ⊎, and ^ relate to the basic type formers
-- in functional programming and their cardinality
embed : ∀ (n m : ℕ) -> Fin n -> Fin (m + n)
embed n zero f = f
embed n (suc m) f = fs (embed n m f)

lem1 : Fin n ⊎ Fin m -> Fin (n + m)
lem1 (inj₁ fz)     = fz
lem1 (inj₁ (fs x)) = fs (lem1 (inj₁ x))
lem1 (inj₂ y)      = embed _ _ y

lem2 : (n m : ℕ) -> Fin (n + m) -> Fin n ⊎ Fin m
lem2 zero m f = inj₂ f
lem2 (suc n) m fz = inj₁ fz
lem2 (suc n) m (fs f) = Data.Sum.map fs (λ x -> x) (lem2 n m f)

-- There's a lot more possible correspondences too!
-- ===
-- Path n <=> Fin (2 ^ (n + 1) - 1) <=> Tree Unit n
-- Finite A n × Finite B m <=> Finite (A × B) (n * m)
-- Fin n × Fin m  <=> Fin (n * m)
-- Fin m -> Fin n <=> Fin (n ^ m)
