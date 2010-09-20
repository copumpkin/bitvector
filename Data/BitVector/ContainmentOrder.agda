module Data.BitVector.ContainmentOrder where

open import Data.Empty
open import Data.Sum
open import Data.Vec

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Nat hiding (_≟_; _≤_; _≤?_) renaming (zero to Nzero; suc to Nsuc)

open import Data.BitVector

infix 4 _⊂_

data _⊂_ : ∀ {n} → BitVector n → BitVector n → Set where
  []⊂[] : [] ⊂ []
  0#⊂0# : ∀ {n} {x y : BitVector n}     → (x⊂y : x ⊂ y) → (0# ∷ x) ⊂ (0# ∷ y)
  b⊂1#  : ∀ {n} {x y : BitVector n} {b} → (x⊂y : x ⊂ y) → (b  ∷ x) ⊂ (1# ∷ y)

⊂-refl : ∀ {n} → _≡_ ⇒ (_⊂_ {n})
⊂-refl {0} {[]} refl = []⊂[]
⊂-refl {Nsuc n} {0# ∷ xs} refl = 0#⊂0# (⊂-refl refl)
⊂-refl {Nsuc n} {1# ∷ xs} refl = b⊂1# (⊂-refl refl)

⊂-antisym : ∀ {n} → Antisymmetric _≡_ (_⊂_ {n})
⊂-antisym []⊂[] []⊂[] = refl
⊂-antisym (0#⊂0# x⊂y) (0#⊂0# y⊂x) rewrite ⊂-antisym x⊂y y⊂x = refl
⊂-antisym (b⊂1#  x⊂y) (b⊂1#  y⊂x) rewrite ⊂-antisym x⊂y y⊂x = refl

⊂-trans : ∀ {n} → Transitive (_⊂_ {n})
⊂-trans []⊂[] []⊂[] = []⊂[]
⊂-trans (0#⊂0# x⊂y) (0#⊂0# y⊂z) = 0#⊂0# (⊂-trans x⊂y y⊂z)
⊂-trans (0#⊂0# x⊂y) (b⊂1#  y⊂z) = b⊂1#  (⊂-trans x⊂y y⊂z)
⊂-trans (b⊂1#  x⊂y) (b⊂1#  y⊂z) = b⊂1#  (⊂-trans x⊂y y⊂z)

_⊂?_ : ∀ {n} → Decidable (_⊂_ {n})
[] ⊂? [] = yes []⊂[]
(x ∷ xs) ⊂? (y ∷ ys) with xs ⊂? ys 
(0# ∷ xs) ⊂? (0# ∷ ys)  | no  xs≢ys = no helper
  where helper : ¬ 0# ∷ xs ⊂ 0# ∷ ys
        helper (0#⊂0# pf) = xs≢ys pf
(x  ∷ xs) ⊂? (1# ∷ ys)  | no  xs≢ys = no helper
  where helper : ¬ x ∷ xs ⊂ 1# ∷ ys
        helper (b⊂1# pf) = xs≢ys pf
(1# ∷ xs) ⊂? (0# ∷ ys)  | no  xs≢ys = no (λ ())
(0# ∷ xs) ⊂? (0# ∷ ys)  | yes xs≡ys = yes (0#⊂0# xs≡ys)
(0# ∷ xs) ⊂? (1# ∷ ys)  | yes xs≡ys = yes (b⊂1#  xs≡ys)
(1# ∷ xs) ⊂? (0# ∷ ys)  | yes xs≡ys = no  (λ ())
(1# ∷ xs) ⊂? (1# ∷ ys)  | yes xs≡ys = yes (b⊂1#  xs≡ys)

decPoset : ∀ {n} → DecPoset _ _ _
decPoset {n} = record
  { Carrier = BitVector n
  ; _≈_ = _≡_
  ; _≤_ = _⊂_
  ; isDecPartialOrder = record
      { isPartialOrder = record 
          { isPreorder = record 
              { isEquivalence = isEquivalence
              ; reflexive = ⊂-refl
              ; trans = ⊂-trans
              }
          ; antisym = ⊂-antisym
          }
      ; _≟_ = _≟_
      ; _≤?_ = _⊂?_
      }
  }