module Data.BitVector.NumericOrder where

open import Data.Empty
open import Data.Sum
open import Data.Vec

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Nat hiding (decTotalOrder; _≟_; _<_; _≤_; _≤?_; compare) renaming (zero to Nzero; suc to Nsuc)

open import Data.BitVector

infix 4 _<_
infix 4 _q≤_ 

mutual
  -- TODO: merge 1#<1# and 0#<0# and 1#≤1# and 0#≤0#. That should clean up the proofs a bit.

  -- Is keeping this inductive (rather than working with suc) really worth it? Check out the transitivity proofs further down :(
  data _<_ : ∀ {n} → BitVector n → BitVector n → Set where
    b#<b# : ∀ {n} {x y : BitVector n} {b#} → (pf : x < y) → (b# ∷ x) < (b# ∷ y)

    0#<1# : ∀ {n} {x y : BitVector n} → (pf : x q≤ y) → (0# ∷ x) < (1# ∷ y)
    1#<0# : ∀ {n} {x y : BitVector n} → (pf : x < y) → (1# ∷ x) < (0# ∷ y)

  -- Silly agda bug is preventing me from using the _≤_ name even though it's not in scope :(
  data _q≤_ : ∀ {n} → BitVector n → BitVector n → Set where
    []≤[] : [] q≤ []
    b#≤b# : ∀ {n} {x y : BitVector n} {b#} → (pf : x q≤ y) → (b# ∷ x) q≤ (b# ∷ y)
  
    0#≤1# : ∀ {n} {x y : BitVector n} → (pf : x q≤ y) → (0# ∷ x) q≤ (1# ∷ y)
    1#≤0# : ∀ {n} {x y : BitVector n} → (pf : x <  y) → (1# ∷ x) q≤ (0# ∷ y)

<-irr : ∀ {n} {x : BitVector n} → ¬ x < x
<-irr {0} ()
<-irr (b#<b# pf) = <-irr pf

≤-refl : ∀ {n} → _≡_ ⇒ (_q≤_ {n})
≤-refl {0} {[]} refl = []≤[]
≤-refl {Nsuc n} {b# ∷ xs} refl = b#≤b# (≤-refl refl)


opposites : ∀ {n} {x y : BitVector n} → x q≤ y → y < x → ⊥
opposites []≤[] ()
opposites (b#≤b# pf₀) (b#<b# pf₁) = opposites pf₀ pf₁
opposites (0#≤1# pf₀) (1#<0# pf₁) = opposites pf₀ pf₁
opposites (1#≤0# pf₀) (0#<1# pf₁) = opposites pf₁ pf₀


≤-antisym : ∀ {n} → Antisymmetric _≡_ (_q≤_ {n})
≤-antisym []≤[] q = refl
≤-antisym (b#≤b# pf₀) (b#≤b# pf₁) rewrite ≤-antisym pf₀ pf₁ = refl
≤-antisym (0#≤1# (b#≤b# pf₀)) (1#≤0# (b#<b# pf₁)) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (0#≤1# (1#≤0# pf₀)) (1#≤0# (0#<1# pf₁)) = ⊥-elim (opposites pf₁ pf₀)
≤-antisym (0#≤1# (0#≤1# pf₀)) (1#≤0# (1#<0# pf₁)) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (0#≤1# pf₀) (1#≤0# pf₁) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (1#≤0# pf₀) (0#≤1# pf₁) = ⊥-elim (opposites pf₁ pf₀)

mutual
  ≤-<-trans-< : ∀ {n} {x y z : BitVector n} → x q≤ y → y < z → x < z
  ≤-<-trans-< []≤[] ()
  ≤-<-trans-< (b#≤b# pf₀) (b#<b# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (b#≤b# pf₀) (0#<1# pf₁) = 0#<1# (≤-trans pf₀ pf₁)
  ≤-<-trans-< (b#≤b# pf₀) (1#<0# pf₁) = 1#<0# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (0#≤1# pf₀) (b#<b# pf₁) = 0#<1# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-< (0#≤1# pf₀) (1#<0# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (1#≤0# pf₀) (b#<b# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  ≤-<-trans-< (1#≤0# pf₀) (0#<1# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)

  <-≤-trans-< : ∀ {n} {x y z : BitVector n} → x < y → y q≤ z → x < z
  <-≤-trans-< (b#<b# pf₀) (b#≤b# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)
  <-≤-trans-< (b#<b# pf₀) (0#≤1# pf₁) = 0#<1# (<-≤-trans-≤ pf₀ pf₁)
  <-≤-trans-< (b#<b# pf₀) (1#≤0# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  <-≤-trans-< (0#<1# pf₀) (b#≤b# pf₁) = 0#<1# (≤-trans pf₀ pf₁)
  <-≤-trans-< (0#<1# pf₀) (1#≤0# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  <-≤-trans-< (1#<0# pf₀) (b#≤b# pf₁) = 1#<0# (<-≤-trans-< pf₀ pf₁)
  <-≤-trans-< (1#<0# pf₀) (0#≤1# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)

  ≤-<-trans-≤ : ∀ {n} {x y z : BitVector n} → x q≤ y → y < z → x q≤ z
  ≤-<-trans-≤ []≤[] ()
  ≤-<-trans-≤ (b#≤b# pf₀) (b#<b# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (b#≤b# pf₀) (0#<1# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-<-trans-≤ (b#≤b# pf₀) (1#<0# pf₁) = 1#≤0# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-≤ (0#≤1# pf₀) (b#<b# pf₁) = 0#≤1# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (0#≤1# pf₀) (1#<0# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (1#≤0# pf₀) (b#<b# pf₁) = 1#≤0# (<-trans pf₀ pf₁)
  ≤-<-trans-≤ (1#≤0# pf₀) (0#<1# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)

  <-≤-trans-≤ : ∀ {n} {x y z : BitVector n} → x < y → y q≤ z → x q≤ z
  <-≤-trans-≤ (b#<b# pf₀) (b#≤b# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)
  <-≤-trans-≤ (b#<b# pf₀) (0#≤1# pf₁) = 0#≤1# (<-≤-trans-≤ pf₀ pf₁)
  <-≤-trans-≤ (b#<b# pf₀) (1#≤0# pf₁) = 1#≤0# (<-trans pf₀ pf₁)
  <-≤-trans-≤ (0#<1# pf₀) (b#≤b# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  <-≤-trans-≤ (0#<1# pf₀) (1#≤0# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  <-≤-trans-≤ (1#<0# pf₀) (b#≤b# pf₁) = 1#≤0# (<-≤-trans-< pf₀ pf₁)
  <-≤-trans-≤ (1#<0# pf₀) (0#≤1# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)

  <-trans : ∀ {n} → Transitive (_<_ {n})
  <-trans (b#<b# pf₀) (b#<b# pf₁) = b#<b# (<-trans pf₀ pf₁)
  <-trans (b#<b# pf₀) (0#<1# pf₁) = 0#<1# (<-≤-trans-≤ pf₀ pf₁)
  <-trans (b#<b# pf₀) (1#<0# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  <-trans (0#<1# pf₀) (b#<b# pf₁) = 0#<1# (≤-<-trans-≤ pf₀ pf₁)
  <-trans (0#<1# pf₀) (1#<0# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  <-trans (1#<0# pf₀) (b#<b# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  <-trans (1#<0# pf₀) (0#<1# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)

  ≤-trans : ∀ {n} → Transitive (_q≤_ {n})
  ≤-trans []≤[] []≤[] = []≤[]
  ≤-trans (b#≤b# pf₀) (b#≤b# pf₁) = b#≤b# (≤-trans pf₀ pf₁)
  ≤-trans (b#≤b# pf₀) (0#≤1# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-trans (b#≤b# pf₀) (1#≤0# pf₁) = 1#≤0# (≤-<-trans-< pf₀ pf₁)
  ≤-trans (0#≤1# pf₀) (b#≤b# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-trans (0#≤1# pf₀) (1#≤0# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-trans (1#≤0# pf₀) (b#≤b# pf₁) = 1#≤0# (<-≤-trans-< pf₀ pf₁)
  ≤-trans (1#≤0# pf₀) (0#≤1# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)


<⇒≤ : ∀ {n} {x y : BitVector n} → x < y → x q≤ y
<⇒≤ (b#<b# pf) = b#≤b# (<⇒≤ pf)
<⇒≤ (0#<1# pf) = 0#≤1# pf
<⇒≤ (1#<0# pf) = 1#≤0# pf


≤⇒≡⊎< : ∀ {n} → {x y : BitVector n} → x q≤ y → x ≡ y ⊎ x < y
≤⇒≡⊎< []≤[] = inj₁ refl
≤⇒≡⊎< (b#≤b# pf) with ≤⇒≡⊎< pf
...                 | inj₁ refl = inj₁ refl
...                 | inj₂ x<y = inj₂ (b#<b# x<y)
≤⇒≡⊎< (0#≤1# pf) = inj₂ (0#<1# pf)
≤⇒≡⊎< (1#≤0# pf) = inj₂ (1#<0# pf)


compare : ∀ {n} → Trichotomous _≡_ (_<_ {n})
compare [] [] = tri≈ (λ ()) refl (λ ())
compare (x ∷ xs) (y ∷ ys) with compare xs ys 
compare (0# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = tri< (b#<b# a) (λ xs≡ys → ¬b (cong tail xs≡ys)) helper
  where helper : ¬ (0# ∷ ys) < (0# ∷ xs)
        helper (b#<b# pf) = ¬c pf
compare (0# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = tri< (0#<1# (<⇒≤ a)) (λ xs≡ys → ¬b (cong tail xs≡ys)) helper
  where helper : ¬ (1# ∷ ys) < (0# ∷ xs)
        helper (1#<0# pf) = ¬c pf
compare (1# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = tri< (1#<0# a) (λ xs≡ys → ¬b (cong tail xs≡ys)) helper
  where helper : ¬ (0# ∷ ys) < (1# ∷ xs)
        helper (0#<1# pf) with ≤⇒≡⊎< pf
        ...                  | inj₁ x≡y = ¬b (sym x≡y)
        ...                  | inj₂ x<y = ¬c x<y
compare (1# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = tri< (b#<b# a) (λ xs≡ys → ¬b (cong tail xs≡ys)) helper
  where helper : ¬ (1# ∷ ys) < (1# ∷ xs)
        helper (b#<b# pf) = ¬c pf
compare (0# ∷ xs) (0# ∷ ys) | tri≈ ¬a b ¬c rewrite b = tri≈ <-irr refl <-irr
compare (0# ∷ xs) (1# ∷ ys) | tri≈ ¬a b ¬c rewrite b = tri< (0#<1# (≤-refl refl)) (λ ()) helper
  where helper : ¬ (1# ∷ ys) < (0# ∷ ys)
        helper (1#<0# pf) = ¬c pf
compare (1# ∷ xs) (0# ∷ ys) | tri≈ ¬a b ¬c rewrite b = tri> helper (λ ()) (0#<1# (≤-refl refl))
  where helper : ¬ (1# ∷ ys) < (0# ∷ ys)
        helper (1#<0# pf) = ¬a pf
compare (1# ∷ xs) (1# ∷ ys) | tri≈ ¬a b ¬c rewrite b = tri≈ <-irr refl <-irr
compare (0# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = tri> helper  (λ xs≡ys → ¬b (cong tail xs≡ys)) (b#<b# c) 
  where helper : ¬ (0# ∷ xs) < (0# ∷ ys)
        helper (b#<b# pf) = ¬a pf
compare (0# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = tri> helper (λ ()) (1#<0# c)
  where helper : ¬ (0# ∷ xs) < (1# ∷ ys)
        helper (0#<1# pf) with ≤⇒≡⊎< pf
        ...                  | inj₁ x≡y = ¬b x≡y
        ...                  | inj₂ x<y = ¬a x<y
compare (1# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = tri> helper (λ ()) (0#<1# (<⇒≤ c)) 
  where helper : ¬ (1# ∷ xs) < (0# ∷ ys)
        helper (1#<0# pf) = ¬a pf
compare (1# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = tri> helper  (λ xs≡ys → ¬b (cong tail xs≡ys)) (b#<b# c) 
  where helper : ¬ (1# ∷ xs) < (1# ∷ ys)
        helper (b#<b# pf) = ¬a pf

≤-total : ∀ {n} → Total (_q≤_ {n})
≤-total [] [] = inj₁ []≤[]
≤-total (x  ∷ xs) (y  ∷ ys) with compare xs ys 
≤-total (0# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = inj₁ (b#≤b# (<⇒≤ a))
≤-total (0# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = inj₁ (0#≤1# (<⇒≤ a))
≤-total (1# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = inj₁ (1#≤0# a)
≤-total (1# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = inj₁ (b#≤b# (<⇒≤ a))
≤-total (0# ∷ xs) (0# ∷ ys) | tri≈ ¬a b ¬c = inj₁ (b#≤b# (≤-refl b))
≤-total (0# ∷ xs) (1# ∷ ys) | tri≈ ¬a b ¬c = inj₁ (0#≤1# (≤-refl b))
≤-total (1# ∷ xs) (0# ∷ ys) | tri≈ ¬a b ¬c = inj₂ (0#≤1# (≤-refl (sym b)))
≤-total (1# ∷ xs) (1# ∷ ys) | tri≈ ¬a b ¬c = inj₁ (b#≤b# (≤-refl b))
≤-total (0# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = inj₂ (b#≤b# (<⇒≤ c))
≤-total (0# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = inj₂ (1#≤0# c)
≤-total (1# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = inj₂ (0#≤1# (<⇒≤ c))
≤-total (1# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = inj₂ (b#≤b# (<⇒≤ c))


_≤?_ : ∀ {n} → Decidable (_q≤_ {n})
x ≤? y with compare x y
...       | tri< a ¬b ¬c = yes (<⇒≤ a)
...       | tri≈ ¬a b ¬c = yes (≤-refl b)
...       | tri> ¬a ¬b c = no  helper
  where helper : ¬ x q≤ y
        helper x≤y with ≤⇒≡⊎< x≤y
        ...           | inj₁ x≡y = ¬b x≡y 
        ...           | inj₂ x<y = ¬a x<y

decTotalOrder : ∀ {n} → DecTotalOrder _ _ _
decTotalOrder {n} = record
  { Carrier         = BitVector n
  ; _≈_             = _≡_
  ; _≤_             = _q≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
        { isPartialOrder = record
          { isPreorder = record
              { isEquivalence = isEquivalence
              ; reflexive     = ≤-refl
              ; trans         = ≤-trans
              }
            ; antisym  = ≤-antisym
            }
            ; total = ≤-total
            }
          ; _≟_  = _≟_
          ; _≤?_ = _≤?_
          }
    }

strictTotalOrder : ∀ {n} → StrictTotalOrder _ _ _
strictTotalOrder {n} = record
  { Carrier            = BitVector n
  ; _≈_                = _≡_
  ; _<_                = _<_
  ; isStrictTotalOrder = record
      { isEquivalence = isEquivalence
      ; trans         = <-trans
      ; compare       = compare
      ; <-resp-≈      = resp₂ _<_
      }
  }
