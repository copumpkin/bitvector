module Properties where

open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties.Core
open import Algebra
open import Algebra.Structures

open import Data.Product
open import Data.Nat using (ℕ) renaming (zero to Nzero; suc to Nsuc)
open import Data.Vec

open import Data.Bool renaming (Bool to Bit; false to 0#; true to 1#)
open import Data.Bool.Properties renaming (isBooleanAlgebra to Bool-isBooleanAlgebra)

open import BitVector

module BitProperties = IsBooleanAlgebra Bool-isBooleanAlgebra

module LatticeProperties (n : ℕ) where
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

module Properties {n : ℕ} where
  identityˡ : ∀ {n} x → zero n + x ≡ x
  identityˡ [] = refl
  identityˡ (1# ∷ xs) rewrite identityˡ xs = refl
  identityˡ (0# ∷ xs) rewrite identityˡ xs = refl

  identityʳ : ∀ {n} x → x + zero n ≡ x
  identityʳ [] = refl
  identityʳ (1# ∷ xs) rewrite identityʳ xs = refl
  identityʳ (0# ∷ xs) rewrite identityʳ xs = refl


  identity = identityˡ , identityʳ

  add-carry : ∀ {n} c₁ c₂ (x y z : BitVector n) → add′ c₁ x (add′ c₂ y z) ≡ add′ c₂ x (add′ c₁ y z)
  add-carry c₁ c₂ [] [] [] = refl
  add-carry 0# 0# (0# ∷ xs) (y     ∷ ys) (z     ∷ zs) = refl
  add-carry 0# 0# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 0# 0# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) = refl
  add-carry 0# 0# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) = refl
  add-carry 0# 0# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl
  add-carry 0# 1# (0# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 0# 1# (0# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-carry 0# 1# xs ys zs = refl
  add-carry 0# 1# (0# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-carry 0# 1# xs ys zs = refl
  add-carry 0# 1# (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl
  add-carry 0# 1# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 0# 1# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-carry 0# 1# xs ys zs = refl
  add-carry 0# 1# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-carry 0# 1# xs ys zs = refl
  add-carry 0# 1# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl
  add-carry 1# 0# (0# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 1# 0# (0# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-carry 1# 0# xs ys zs = refl
  add-carry 1# 0# (0# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-carry 1# 0# xs ys zs = refl
  add-carry 1# 0# (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl
  add-carry 1# 0# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 1# 0# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-carry 1# 0# xs ys zs = refl
  add-carry 1# 0# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-carry 1# 0# xs ys zs = refl
  add-carry 1# 0# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl
  add-carry 1# 1# (0# ∷ xs) (y     ∷ ys) (z     ∷ zs) = refl
  add-carry 1# 1# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) = refl
  add-carry 1# 1# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) = refl
  add-carry 1# 1# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) = refl
  add-carry 1# 1# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) = refl


  add-assoc : ∀ {n} c₁ c₂ (x y z : BitVector n) → add′ c₁ (add′ c₂ x y) z ≡ add′ c₁ x (add′ c₂ y z)
  add-assoc c₁ c₂ [] [] [] = refl
  add-assoc c₁ 1# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 1# xs ys zs = refl
  add-assoc c₁ 1# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc c₁ 1# xs ys zs = refl
  add-assoc c₁ 1# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc c₁ 1# xs ys zs = refl
  add-assoc c₁ 1# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 1# xs ys zs | add-carry 0# 1# xs ys zs = refl
  add-assoc c₁ 1# (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc c₁ 1# xs ys zs = refl
  add-assoc c₁ 1# (0# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 1# xs ys zs = refl
  add-assoc c₁ 1# (0# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 0# xs ys zs | add-carry 1# 0# xs ys zs = refl
  add-assoc c₁ 1# (0# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc c₁ 0# xs ys zs = refl
  add-assoc c₁ 0# (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc c₁ 1# xs ys zs = refl
  add-assoc c₁ 0# (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 1# xs ys zs | add-carry 0# 1# xs ys zs = refl
  add-assoc c₁ 0# (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 0# xs ys zs = refl
  add-assoc c₁ 0# (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc c₁ 0# xs ys zs = refl
  add-assoc c₁ 0# (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 0# xs ys zs | add-carry 1# 0# xs ys zs = refl
  add-assoc c₁ 0# (0# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc c₁ 0# xs ys zs = refl
  add-assoc c₁ 0# (0# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc c₁ 0# xs ys zs = refl
  add-assoc c₁ 0# (0# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 0# xs ys zs = refl

  assoc : ∀ {n} (x y z : BitVector n) → (x + y) + z ≡ x + (y + z)
  assoc [] [] [] = refl
  assoc (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc 0# 1# xs ys zs = refl
  assoc (1# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 1# xs ys zs | add-carry 0# 1# xs ys zs = refl
  assoc (1# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 0# xs ys zs = refl
  assoc (1# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 0# xs ys zs = refl
  assoc (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite add-assoc 1# 0# xs ys zs | add-carry 1# 0# xs ys zs = refl
  assoc (0# ∷ xs) (1# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 0# xs ys zs = refl
  assoc (0# ∷ xs) (0# ∷ ys) (1# ∷ zs) rewrite add-assoc 0# 0# xs ys zs = refl
  assoc (0# ∷ xs) (0# ∷ ys) (0# ∷ zs) rewrite add-assoc 0# 0# xs ys zs = refl
  
  add-comm : ∀ {n} c (x y : BitVector n) → add′ c x y ≡ add′ c y x
  add-comm c [] [] = refl
  add-comm c (1# ∷ xs) (1# ∷ ys) rewrite add-comm 1# xs ys = refl
  add-comm c (1# ∷ xs) (0# ∷ ys) rewrite add-comm c xs ys = refl
  add-comm c (0# ∷ xs) (1# ∷ ys) rewrite add-comm c xs ys = refl
  add-comm c (0# ∷ xs) (0# ∷ ys) rewrite add-comm 0# xs ys = refl

  comm : ∀ {n} (x y : BitVector n) → x + y ≡ y + x
  comm = add-comm 0#

  add-inverse : ∀ {n} xs → add′ 1# (add′ 0# (zero n) (bitwise-negation xs)) xs ≡ zero n
  add-inverse [] = refl
  add-inverse (1# ∷ xs) rewrite add-inverse xs = refl
  add-inverse (0# ∷ xs) rewrite add-inverse xs = refl

  inverseˡ : ∀ {n} (x : BitVector n) → - x + x ≡ zero n
  inverseˡ [] = refl
  inverseˡ (1# ∷ xs) rewrite add-inverse xs = refl
  inverseˡ (0# ∷ xs) rewrite add-assoc 0# 1# (zero _) (bitwise-negation xs) xs
                              | add-carry 0# 1# (zero _) (bitwise-negation xs) xs
                              | sym (add-assoc 1# 0# (zero _) (bitwise-negation xs) xs)
                              | add-inverse xs = refl

  inverseʳ : ∀ {n} (x : BitVector n) → x + - x ≡ zero n
  inverseʳ x = trans (comm x (- x)) (inverseˡ x)





  *-zeroˡ : ∀ {n} (x : BitVector n) → zero n * x ≡ zero n
  *-zeroˡ [] = refl
  *-zeroˡ (x ∷ xs) rewrite *-zeroˡ (droplast (x ∷ xs)) = refl

  *-identityˡ : ∀ {n} (x : BitVector n) → one n * x ≡ x
  *-identityˡ [] = refl
  *-identityˡ (0# ∷ xs) rewrite *-zeroˡ (droplast (0# ∷ xs)) | identityʳ xs = refl
  *-identityˡ (1# ∷ xs) rewrite *-zeroˡ (droplast (1# ∷ xs)) | identityʳ xs = refl

  mutual
   *-comm : ∀ {n} (x y : BitVector n) → x * y ≡ y * x
   *-comm {Nzero} [] [] = refl
   *-comm {Nsuc n} x y = *-comm1 x y

   *-comm1 : ∀ {n} (x y : BitVector (Nsuc n)) → x * y ≡ y * x
   *-comm1 (0# ∷ []) (0# ∷ []) = refl
   *-comm1 (0# ∷ []) (1# ∷ []) = refl
   *-comm1 (1# ∷ []) (0# ∷ []) = refl
   *-comm1 (1# ∷ []) (1# ∷ []) = refl
   *-comm1 {Nsuc n'} (0# ∷ xs) (0# ∷ ys) rewrite *-comm1 xs (0# ∷ droplast ys)
                                               | *-comm1 ys (0# ∷ droplast xs)
                                               | *-comm (droplast ys) (droplast xs) = refl
   *-comm1 {Nsuc n'} (0# ∷ xs) (1# ∷ ys) rewrite *-comm1 xs (1# ∷ droplast ys)
                                               | *-comm1 ys (0# ∷ droplast xs)
                                               | *-comm (droplast ys) (droplast xs) = refl
   *-comm1 {Nsuc n'} (1# ∷ xs) (0# ∷ ys) rewrite *-comm1 xs (0# ∷ droplast ys)
                                               | *-comm1 ys (1# ∷ droplast xs)
                                               | *-comm (droplast ys) (droplast xs) = refl
   *-comm1 {Nsuc n'} (1# ∷ xs) (1# ∷ ys) rewrite *-comm1 xs (1# ∷ droplast ys)
                                               | *-comm1 ys (1# ∷ droplast xs)
                                               | *-comm (droplast ys) (droplast xs)
                                               | sym (assoc ys xs (0# ∷ droplast xs * droplast ys))
                                               | comm ys xs
                                               | assoc xs ys (0# ∷ droplast xs * droplast ys) = refl

  droplast-distrib-+ : ∀ {n} (x y : BitVector (Nsuc n)) → droplast (x + y) ≡ droplast x + droplast y
  droplast-distrib-+ {Nzero} (x ∷ xs) (y ∷ ys) = refl
  droplast-distrib-+ {Nsuc n'} (0# ∷ xs) (0# ∷ ys) rewrite droplast-distrib-+ xs ys = refl
  droplast-distrib-+ {Nsuc n'} (0# ∷ xs) (1# ∷ ys) rewrite droplast-distrib-+ xs ys = refl
  droplast-distrib-+ {Nsuc n'} (1# ∷ xs) (0# ∷ ys) rewrite droplast-distrib-+ xs ys = refl
  droplast-distrib-+ {Nsuc n'} (1# ∷ xs) (1# ∷ ys) rewrite droplast-distrib-+ xs ys = cong (_∷_ 0#) (lemma xs ys)
   where
   lemma : ∀ {n} (xs ys : BitVector (Nsuc n)) → droplast (add′ 1# xs ys) ≡ add′ 1# (droplast xs) (droplast ys)
   lemma {Nzero} (x ∷ xs') (y ∷ ys') = refl
   lemma {Nsuc _} (0# ∷ xs) (0# ∷ ys) rewrite droplast-distrib-+ xs ys = refl
   lemma {Nsuc _} (0# ∷ xs) (1# ∷ ys) rewrite lemma xs ys = refl
   lemma {Nsuc _} (1# ∷ xs) (0# ∷ ys) rewrite lemma xs ys = refl
   lemma {Nsuc _} (1# ∷ xs) (1# ∷ ys) rewrite lemma xs ys = refl

  droplast-distrib-* : ∀ {n} (x y : BitVector (Nsuc n)) → droplast (x * y) ≡ droplast x * droplast y
  droplast-distrib-* {Nzero} _ _ = refl
  droplast-distrib-* {Nsuc _} (0# ∷ xs) (y  ∷ ys) rewrite droplast-distrib-* xs (y ∷ droplast ys) = refl
  droplast-distrib-* {Nsuc _} (1# ∷ xs) (0# ∷ ys) rewrite droplast-distrib-+ ys (xs * (0# ∷ droplast ys))
                                                        | droplast-distrib-* xs (0# ∷ droplast ys) = refl
  droplast-distrib-* {Nsuc _} (1# ∷ xs) (1# ∷ ys) rewrite droplast-distrib-+ ys (xs * (1# ∷ droplast ys))
                                                        | droplast-distrib-* xs (1# ∷ droplast ys) = refl

  extract-carry : ∀ {n} (xs ys : BitVector n) → add′ 1# xs ys ≡ one _ + add′ 0# xs ys
  extract-carry [] [] = refl
  extract-carry (0# ∷ xs) (0# ∷ ys) rewrite identityˡ (xs + ys) = refl
  extract-carry (0# ∷ xs) (1# ∷ ys) rewrite add-carry 1# 0# (zero _) xs ys | identityˡ (add′ 1# xs ys) = refl
  extract-carry (1# ∷ xs) (0# ∷ ys) rewrite add-carry 1# 0# (zero _) xs ys | identityˡ (add′ 1# xs ys) = refl
  extract-carry (1# ∷ xs) (1# ∷ ys) rewrite identityˡ (add′ 1# xs ys) = refl


  shift-to-add : ∀ c {n} (x : BitVector n) → droplast (c ∷ x) ≡ add′ c x x
  shift-to-add _ [] = refl
  shift-to-add c (0# ∷ xs) rewrite shift-to-add 0# xs = refl
  shift-to-add c (1# ∷ xs) rewrite shift-to-add 1# xs = refl

  *-distribʳ : ∀ {n} (x y z : BitVector n) → (y + z) * x ≡ (y * x) + (z * x)
  *-distribʳ [] [] [] = refl
  *-distribʳ {Nsuc n} xs ys zs = *-distribʳ1 xs ys zs

    where
    lemma : ∀ {n} c (xs ys zs : BitVector n) → add′ 1# ys zs * droplast (c ∷ xs) ≡  add′ c (xs + (ys * droplast (c ∷ xs))) (xs + (zs * droplast (c ∷ xs)))
    lemma c xs ys zs rewrite extract-carry ys zs
                           | *-distribʳ (droplast (c ∷ xs)) (one _) (ys + zs)
                           | *-identityˡ (droplast (c ∷ xs))
                           | *-distribʳ (droplast (c ∷ xs)) ys zs
                           | shift-to-add c xs
                           | *-comm ys (add′ c xs xs)
                           | *-comm zs (add′ c xs xs)
                           | comm (add′ c xs xs) (add′ 0# (add′ c xs xs * ys) (add′ c xs xs * zs))
                           | add-carry 0# c (add′ 0# (add′ c xs xs * ys) (add′ c xs xs * zs)) xs xs
                           | add-assoc c 0# (add′ c xs xs * ys) (add′ c xs xs * zs) (xs + xs)
                           | sym (add-assoc 0# 0# (add′ c xs xs * zs) xs xs)
                           | comm (add′ c xs xs * zs) xs
                           | comm (add′ 0# xs (add′ c xs xs * zs)) xs
                           | sym (add-assoc c 0# (add′ c xs xs * ys) xs (add′ 0# xs (add′ c xs xs * zs)))
                           | comm  (add′ c xs xs * ys) xs
      = refl


    *-distribʳ1 : ∀ {n} (x y z : BitVector (Nsuc n)) → (y + z) * x ≡ (y * x) + (z * x)
    *-distribʳ1 xs (0# ∷ ys) (0# ∷ zs) rewrite *-distribʳ (droplast xs) ys zs = refl
    *-distribʳ1 (0# ∷ xs) (0# ∷ ys) (1# ∷ zs)
             rewrite *-distribʳ (droplast (0# ∷ xs)) ys zs
                   | sym (assoc xs (ys * droplast (0# ∷ xs)) (zs * droplast (0# ∷ xs)))
                   | comm xs (ys * droplast (0# ∷ xs))
                   | assoc (ys * droplast (0# ∷ xs)) xs (zs * droplast (0# ∷ xs)) = refl
    *-distribʳ1 (1# ∷ xs) (0# ∷ ys) (1# ∷ zs)
             rewrite *-distribʳ (droplast (1# ∷ xs)) ys zs
                   | sym (assoc xs (ys * droplast (1# ∷ xs)) (zs * droplast (1# ∷ xs)))
                   | comm xs (ys * droplast (1# ∷ xs))
                   | assoc (ys * droplast (1# ∷ xs)) xs (zs * droplast (1# ∷ xs)) = refl
    *-distribʳ1 (0# ∷ xs) (1# ∷ ys) (0# ∷ zs)
             rewrite *-distribʳ (droplast (0# ∷ xs)) ys zs
                   | assoc xs (ys * droplast (0# ∷ xs)) (zs * droplast (0# ∷ xs)) = refl
    *-distribʳ1 (1# ∷ xs) (1# ∷ ys) (0# ∷ zs)
             rewrite *-distribʳ (droplast (1# ∷ xs)) ys zs
                   | assoc xs (ys * droplast (1# ∷ xs)) (zs * droplast (1# ∷ xs)) = refl
    *-distribʳ1 (0# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite lemma 0# xs ys zs = refl
    *-distribʳ1 (1# ∷ xs) (1# ∷ ys) (1# ∷ zs) rewrite lemma 1# xs ys zs = refl



  *-assoc : ∀ {n} (x y z : BitVector n) → (x * y) * z ≡ x * (y * z)
  *-assoc [] [] [] = refl
  *-assoc {Nsuc n} x y z = *-assoc1 x y z

   where
   *-assoc1 : ∀ {n} (x y z : BitVector (Nsuc n)) → (x * y) * z ≡ x * (y * z)
   *-assoc1 (0# ∷ xs) ys zs rewrite *-assoc xs (droplast ys) (droplast zs)
                                  | droplast-distrib-* ys zs = refl
   *-assoc1 (1# ∷ xs) ys zs rewrite *-distribʳ zs ys (0# ∷ xs * droplast ys)
                                  | *-assoc xs (droplast ys) (droplast zs)
                                  | droplast-distrib-* ys zs = refl

  *-identityʳ : ∀ {n} (x : BitVector n) → x * one n ≡ x
  *-identityʳ x rewrite *-comm x (one _) = *-identityˡ x

  *-distribˡ : ∀ {n} (x y z : BitVector n) → x * (y + z) ≡ (x * y) + (x * z)
  *-distribˡ x y z rewrite *-comm x (y + z) | *-distribʳ x y z | *-comm x y | *-comm x z = refl

  isSemigroup : IsSemigroup _≡_ _+_
  isSemigroup = record { isEquivalence = isEquivalence; assoc = assoc; ∙-cong = cong₂ _+_ }


  isMonoid : IsMonoid _≡_ _+_ (zero n)
  isMonoid = record { isSemigroup = isSemigroup; identity = identity }


  isGroup : IsGroup _≡_ _+_ (zero n) -_
  isGroup = record { isMonoid = isMonoid; inverse = inverseˡ , inverseʳ; ⁻¹-cong = cong -_ }

  isAbelianGroup : IsAbelianGroup _≡_ _+_ (zero n) -_
  isAbelianGroup = record { isGroup = isGroup; comm = comm }

  *-isSemigroup : IsSemigroup _≡_ _*_
  *-isSemigroup = record { isEquivalence = isEquivalence; assoc = *-assoc; ∙-cong = cong₂ _*_ }

  *-isMonoid : IsMonoid _≡_ _*_ (one n)
  *-isMonoid = record { isSemigroup = *-isSemigroup; identity = *-identityˡ , *-identityʳ }

  isRing : IsRing _≡_ _+_ _*_ -_ (zero n) (one n)
  isRing = record { +-isAbelianGroup = isAbelianGroup; *-isMonoid = *-isMonoid; distrib = *-distribˡ , *-distribʳ }

  isCommutativeRing : IsCommutativeRing _≡_ _+_ _*_ -_ (zero n) (one n)
  isCommutativeRing = record { isRing = isRing; *-comm = *-comm }

  commutativeRing : CommutativeRing _ _
  commutativeRing = record {
                       Carrier = BitVector n;
                       _≈_ = _≡_;
                       _+_ = _+_;
                       _*_ = _*_;
                       -_ = -_;
                       0# = zero n;
                       1# = one n;
                       isCommutativeRing = isCommutativeRing }
