module Data.BitVector.Peano where

open import Data.BitVector
open import Algebra.FunctionProperties.Core
open import Data.Nat hiding (pred) renaming (suc to Nsuc; zero to Nzero)
open import Data.Vec
open import Relation.Binary.PropositionalEquality
suc : ∀ {n} → Op₁ (BitVector n)
suc [] = []
suc (0# ∷ xs) = 1# ∷ xs
suc (1# ∷ xs) = 0# ∷ suc xs

pred-helper : ∀ {n} → BitVector n → BitVector (Nsuc n)
pred-helper [] = 1# ∷ []
pred-helper (0# ∷ xs) = 1# ∷ pred-helper xs
pred-helper (1# ∷ xs) = 1# ∷ 0# ∷ xs

pred : ∀ {n} → Op₁ (BitVector n)
pred [] = []
pred (1# ∷ xs) = 0# ∷ xs
pred (0# ∷ xs) = pred-helper xs

suc∘pred-helper≡0# : ∀ {n} (x : BitVector n) → suc (pred-helper x) ≡ 0# ∷ x
suc∘pred-helper≡0# [] = refl
suc∘pred-helper≡0# (0# ∷ xs) = cong (_∷_ 0#) (suc∘pred-helper≡0# xs)
suc∘pred-helper≡0# (1# ∷ xs) = refl

pred-helper∘suc≡1# : ∀ {n} (x : BitVector n) → pred-helper (suc x) ≡ 1# ∷ x
pred-helper∘suc≡1# [] = refl
pred-helper∘suc≡1# (0# ∷ xs) = refl
pred-helper∘suc≡1# (1# ∷ xs) = cong (_∷_ 1#) (pred-helper∘suc≡1# xs)

suc∘pred≡id : ∀ {n} (x : BitVector n) → suc (pred x) ≡ x
suc∘pred≡id [] = refl
suc∘pred≡id (0# ∷ xs) = suc∘pred-helper≡0# xs
suc∘pred≡id (1# ∷ xs) = refl

pred∘suc≡id : ∀ {n} (x : BitVector n) → pred (suc x) ≡ x
pred∘suc≡id [] = refl
pred∘suc≡id (0# ∷ xs) = refl
pred∘suc≡id (1# ∷ xs) = pred-helper∘suc≡1# xs


data Peano : ∀ {n} → BitVector n → Set where
  Pzero : ∀ {n} → Peano (zero n)
  Psuc  : ∀ {n} {x : BitVector n} → (p : Peano x) → Peano (suc x)

Pdouble : ∀ {n} {x : BitVector n} → Peano x → Peano (0# ∷ x)
Pdouble Pzero = Pzero
Pdouble (Psuc p) = Psuc (Psuc (Pdouble p))


toPeano : ∀ {n} (x : BitVector n) → Peano x
toPeano [] = Pzero
toPeano (0# ∷ xs) = Pdouble (toPeano xs)
toPeano (1# ∷ xs) = Psuc (Pdouble (toPeano xs))

peanoInduction : ∀ {n} → (P : ∀ {x : BitVector n} → Peano x → Set) → P Pzero → (∀ {x : BitVector n} {m : Peano x} → P m → P (Psuc m)) → ∀ {x : BitVector n} (q : Peano x) → P q
peanoInduction P z s Pzero = z
peanoInduction P z s (Psuc p) = s {_} {p} (peanoInduction P z s p)

induction : ∀ {n} (P : BitVector n → Set) → P (zero n) → (∀ {m} → P m → P (suc m)) → ∀ x → P x
induction P z s x = peanoInduction (λ {x} _ → P x) z s (toPeano x) 

toℕ : ∀ {n} → BitVector n → ℕ
toℕ = induction _ 0 Nsuc
