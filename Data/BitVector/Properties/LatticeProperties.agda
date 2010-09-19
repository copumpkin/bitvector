open import Data.Nat using (ℕ)

module Data.BitVector.Properties.LatticeProperties (n : ℕ) where

open import Data.BitVector
open import Algebra.Structures
open import Relation.Binary.PropositionalEquality
open import Data.Vec
open import Data.Product
import Data.Bool.Properties as Bool

private
  module BitProperties = IsBooleanAlgebra Bool.isBooleanAlgebra
  -- All these properties follow trivially from the bit properties. TODO: generalize the pattern to just reuse the bitproperties
  ∨-comm : ∀ {n} (x y : BitVector n) → bitwise-or x y ≡ bitwise-or y x
  ∨-comm [] [] = refl
  ∨-comm (x ∷ xs) (y ∷ ys) rewrite BitProperties.∨-comm x y | ∨-comm xs ys = refl

  ∧-comm : ∀ {n} (x y : BitVector n) → bitwise-and x y ≡ bitwise-and y x
  ∧-comm [] [] = refl
  ∧-comm (x ∷ xs) (y ∷ ys) rewrite BitProperties.∧-comm x y | ∧-comm xs ys = refl

  ∨-assoc : ∀ {n} (x y z : BitVector n) → bitwise-or (bitwise-or x y) z ≡ bitwise-or x (bitwise-or y z)
  ∨-assoc [] [] [] = refl
  ∨-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite BitProperties.∨-assoc x y z | ∨-assoc xs ys zs = refl

  ∧-assoc : ∀ {n} (x y z : BitVector n) → bitwise-and (bitwise-and x y) z ≡ bitwise-and x (bitwise-and y z)
  ∧-assoc [] [] [] = refl
  ∧-assoc (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite BitProperties.∧-assoc x y z | ∧-assoc xs ys zs = refl

  ∨∧-absorb : ∀ {n} (x y : BitVector n) → bitwise-or x (bitwise-and x y) ≡ x
  ∨∧-absorb [] [] = refl
  ∨∧-absorb (x ∷ xs) (y ∷ ys) rewrite proj₁ BitProperties.absorptive x y | ∨∧-absorb xs ys = refl

  ∧∨-absorb : ∀ {n} (x y : BitVector n) → bitwise-and x (bitwise-or x y) ≡ x
  ∧∨-absorb [] [] = refl
  ∧∨-absorb (x ∷ xs) (y ∷ ys) rewrite proj₂ BitProperties.absorptive x y | ∧∨-absorb xs ys = refl

  ∨-cong : ∀ {n} {x y u v : BitVector n} → x ≡ y → u ≡ v → bitwise-or x u ≡ bitwise-or y v
  ∨-cong refl refl = refl

  ∧-cong : ∀ {n} {x y u v : BitVector n} → x ≡ y → u ≡ v → bitwise-and x u ≡ bitwise-and y v
  ∧-cong refl refl = refl
 
  isLattice : ∀ {n} → IsLattice _≡_ (bitwise-or {n}) bitwise-and
  isLattice = record 
    { isEquivalence = isEquivalence
    ; ∨-comm = ∨-comm
    ; ∨-assoc = ∨-assoc
    ; ∨-cong = ∨-cong
    ; ∧-comm = ∧-comm
    ; ∧-assoc = ∧-assoc
    ; ∧-cong = ∧-cong
    ; absorptive = ∨∧-absorb , ∧∨-absorb
    }

  ∨∧-distribʳ : ∀ {n} (x y z : BitVector n) → bitwise-or (bitwise-and y z) x ≡ bitwise-and (bitwise-or y x) (bitwise-or z x)
  ∨∧-distribʳ [] [] [] = refl
  ∨∧-distribʳ (x ∷ xs) (y ∷ ys) (z ∷ zs) rewrite BitProperties.∨-∧-distribʳ x y z | ∨∧-distribʳ xs ys zs = refl
  
  isDistributiveLattice : ∀ {n} → IsDistributiveLattice _≡_ (bitwise-or {n}) bitwise-and
  isDistributiveLattice = record
    { isLattice = isLattice
    ; ∨-∧-distribʳ = ∨∧-distribʳ
    }

  ∨-complementʳ : ∀ {n} (x : BitVector n) → bitwise-or x (bitwise-negation x) ≡ ones n
  ∨-complementʳ [] = refl
  ∨-complementʳ (x ∷ xs) rewrite BitProperties.∨-complementʳ x | ∨-complementʳ xs = refl

  ∧-complementʳ : ∀ {n} (x : BitVector n) → bitwise-and x (bitwise-negation x) ≡ zero n
  ∧-complementʳ [] = refl
  ∧-complementʳ (x ∷ xs) rewrite BitProperties.∧-complementʳ x | ∧-complementʳ xs = refl

  ¬-cong : ∀ {n} {i j : BitVector n} → i ≡ j → bitwise-negation i ≡ bitwise-negation j
  ¬-cong refl = refl

  isBooleanAlgebra : ∀ {n} → IsBooleanAlgebra _≡_ bitwise-or bitwise-and bitwise-negation (ones n) (zero n)
  isBooleanAlgebra = record
    { isDistributiveLattice = isDistributiveLattice
    ; ∨-complementʳ = ∨-complementʳ
    ; ∧-complementʳ = ∧-complementʳ
    ; ¬-cong = ¬-cong
    }
