module Data.BitVector where

open import Data.Vec
open import Data.Nat hiding (pred; decTotalOrder; _≤_; _≟_; _≤?_; _<_; compare) renaming (_+_ to _N+_; _*_ to _N*_; zero to Nzero; suc to Nsuc) 
open import Relation.Binary.PropositionalEquality
open import Algebra.FunctionProperties.Core
open import Data.Product

open import Data.Bool public hiding (_≟_) renaming (Bool to Bit; false to 0#; true to 1#)

infixl 6 _+_
infixl 7 _*_

BitVector = Vec Bit

bitwise-and : ∀ {n} → Op₂ (BitVector n)
bitwise-and = zipWith _∧_

bitwise-or : ∀ {n} → Op₂ (BitVector n)
bitwise-or = zipWith _∨_

half-adder : Bit → Bit → Bit × Bit
half-adder x y = x xor y , x ∧ y

full-adder : Bit → Bit → Bit → Bit × Bit
full-adder a b c0 with half-adder a b
... | s0 , c1 with half-adder s0 c0
... | s1 , c2 = s1 , c1 ∨ c2

add′ : ∀ {n} → Bit → BitVector n → BitVector n → BitVector n
add′ c [] [] = []
add′ c (x ∷ xs) (y ∷ ys) with full-adder x y c
... | s , cout = s ∷ add′ cout xs ys

_+_ : ∀ {n} → Op₂ (BitVector n)
x + y = add′ 0# x y

zero : ∀ n → BitVector n
zero Nzero = []
zero (Nsuc n) = 0# ∷ (zero n)

one : ∀ n → BitVector n
one Nzero = []
one (Nsuc n) = 1# ∷ zero n

bitwise-negation : ∀ {n} → Op₁ (BitVector n)
bitwise-negation = Data.Vec.map not

ones : ∀ n → BitVector n
ones n = bitwise-negation (zero n)

droplast : ∀ {n} → BitVector (Nsuc n) → BitVector n
droplast {Nzero} _ = []
droplast {Nsuc n} (x ∷ xs) = x ∷ droplast xs

shift : ∀ {n} → Op₁ (BitVector n)
shift {Nzero} xs = xs
shift {Nsuc n} xs = 0# ∷ droplast xs


_*_ : ∀ {n} → Op₂ (BitVector n)
[] * [] = []
(0# ∷ xs) * yys = 0# ∷ xs * droplast yys
(1# ∷ xs) * yys = yys + (0# ∷ xs * droplast yys)



-_ : ∀ {n} → Op₁ (BitVector n)
- x = one _ + bitwise-negation x


open import Relation.Nullary
open import Relation.Binary

infix 4 _≟_

_≟_ : ∀ {n} → Decidable {A = BitVector n} _≡_
[] ≟ [] = yes refl
x ∷ xs ≟ y ∷ ys with xs ≟ ys 
0# ∷ xs ≟ 0# ∷ .xs | yes refl = yes refl
1# ∷ xs ≟ 1# ∷ .xs | yes refl = yes refl
1# ∷ xs ≟ 0# ∷ ys  | yes _ = no λ()
0# ∷ xs ≟ 1# ∷ ys  | yes _ = no λ()
...                | no pf = no (λ q → pf (cong tail q))




val1  = 1# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ []
val2  = 0# ∷ 1# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ []
val8  = 0# ∷ 0# ∷ 0# ∷ 1# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ [] 
val10 = 0# ∷ 1# ∷ 0# ∷ 1# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ []
val11 = 1# ∷ 1# ∷ 0# ∷ 1# ∷ 0# ∷ 0# ∷ 0# ∷ 0# ∷ []
