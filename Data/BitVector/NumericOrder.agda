module Data.BitVector.NumericOrder where

open import Data.Empty
open import Data.Sum
open import Data.Vec

open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality

open import Data.Nat hiding (decTotalOrder; _≟_; _<_; _≤_; module _≤_; _≤?_; compare) renaming (zero to Nzero; suc to Nsuc)

open import Data.BitVector

open import Function

infix 4 _<_
infix 4 _≤_ 

mutual
  data _<_ : ∀ {n} → BitVector n → BitVector n → Set where
    b#<b# : ∀ {n} {x y : BitVector n} {b#} → (pf : x < y) → (b# ∷ x) < (b# ∷ y)

    0#<1# : ∀ {n} {x y : BitVector n} → (pf : x ≤ y) → (0# ∷ x) < (1# ∷ y)
    1#<0# : ∀ {n} {x y : BitVector n} → (pf : x < y) → (1# ∷ x) < (0# ∷ y)

  -- Silly agda bug is preventing me from using the _≤_ name even though it's not in scope :(
  data _≤_ : ∀ {n} → BitVector n → BitVector n → Set where
    []≤[] : [] ≤ []
    b#≤b# : ∀ {n} {x y : BitVector n} {b#} → (pf : x ≤ y) → (b# ∷ x) ≤ (b# ∷ y)
  
    0#≤1# : ∀ {n} {x y : BitVector n} → (pf : x ≤ y) → (0# ∷ x) ≤ (1# ∷ y)
    1#≤0# : ∀ {n} {x y : BitVector n} → (pf : x <  y) → (1# ∷ x) ≤ (0# ∷ y)

<-irr : ∀ {n} {x : BitVector n} → ¬ x < x
<-irr {0} ()
<-irr (b#<b# pf) = <-irr pf

≤-refl : ∀ {n} → _≡_ ⇒ (_≤_ {n})
≤-refl {0} {[]} refl = []≤[]
≤-refl {Nsuc n} {b# ∷ xs} refl = b#≤b# (≤-refl refl)


opposites : ∀ {n} {x y : BitVector n} → x ≤ y → y < x → ⊥
opposites []≤[] ()
opposites (b#≤b# pf₀) (b#<b# pf₁) = opposites pf₀ pf₁
opposites (0#≤1# pf₀) (1#<0# pf₁) = opposites pf₀ pf₁
opposites (1#≤0# pf₀) (0#<1# pf₁) = opposites pf₁ pf₀


≤-antisym : ∀ {n} → Antisymmetric _≡_ (_≤_ {n})
≤-antisym []≤[] q = refl
≤-antisym (b#≤b# pf₀) (b#≤b# pf₁) rewrite ≤-antisym pf₀ pf₁ = refl
≤-antisym (0#≤1# (b#≤b# pf₀)) (1#≤0# (b#<b# pf₁)) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (0#≤1# (1#≤0# pf₀)) (1#≤0# (0#<1# pf₁)) = ⊥-elim (opposites pf₁ pf₀)
≤-antisym (0#≤1# (0#≤1# pf₀)) (1#≤0# (1#<0# pf₁)) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (0#≤1# pf₀) (1#≤0# pf₁) = ⊥-elim (opposites pf₀ pf₁)
≤-antisym (1#≤0# pf₀) (0#≤1# pf₁) = ⊥-elim (opposites pf₁ pf₀)

mutual
  ≤-<-trans-< : ∀ {n} {x y z : BitVector n} → x ≤ y → y < z → x < z
  ≤-<-trans-< []≤[] ()
  ≤-<-trans-< (b#≤b# pf₀) (b#<b# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (b#≤b# pf₀) (0#<1# pf₁) = 0#<1# (≤-trans pf₀ pf₁)
  ≤-<-trans-< (b#≤b# pf₀) (1#<0# pf₁) = 1#<0# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (0#≤1# pf₀) (b#<b# pf₁) = 0#<1# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-< (0#≤1# pf₀) (1#<0# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-< (1#≤0# pf₀) (b#<b# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  ≤-<-trans-< (1#≤0# pf₀) (0#<1# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)

  <-≤-trans-< : ∀ {n} {x y z : BitVector n} → x < y → y ≤ z → x < z
  <-≤-trans-< (b#<b# pf₀) (b#≤b# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)
  <-≤-trans-< (b#<b# pf₀) (0#≤1# pf₁) = 0#<1# (<-≤-trans-≤ pf₀ pf₁)
  <-≤-trans-< (b#<b# pf₀) (1#≤0# pf₁) = 1#<0# (<-trans pf₀ pf₁)
  <-≤-trans-< (0#<1# pf₀) (b#≤b# pf₁) = 0#<1# (≤-trans pf₀ pf₁)
  <-≤-trans-< (0#<1# pf₀) (1#≤0# pf₁) = b#<b# (≤-<-trans-< pf₀ pf₁)
  <-≤-trans-< (1#<0# pf₀) (b#≤b# pf₁) = 1#<0# (<-≤-trans-< pf₀ pf₁)
  <-≤-trans-< (1#<0# pf₀) (0#≤1# pf₁) = b#<b# (<-≤-trans-< pf₀ pf₁)

  ≤-<-trans-≤ : ∀ {n} {x y z : BitVector n} → x ≤ y → y < z → x ≤ z
  ≤-<-trans-≤ []≤[] ()
  ≤-<-trans-≤ (b#≤b# pf₀) (b#<b# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (b#≤b# pf₀) (0#<1# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-<-trans-≤ (b#≤b# pf₀) (1#<0# pf₁) = 1#≤0# (≤-<-trans-< pf₀ pf₁)
  ≤-<-trans-≤ (0#≤1# pf₀) (b#<b# pf₁) = 0#≤1# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (0#≤1# pf₀) (1#<0# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-<-trans-≤ (1#≤0# pf₀) (b#<b# pf₁) = 1#≤0# (<-trans pf₀ pf₁)
  ≤-<-trans-≤ (1#≤0# pf₀) (0#<1# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)

  <-≤-trans-≤ : ∀ {n} {x y z : BitVector n} → x < y → y ≤ z → x ≤ z
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

  ≤-trans : ∀ {n} → Transitive (_≤_ {n})
  ≤-trans []≤[] []≤[] = []≤[]
  ≤-trans (b#≤b# pf₀) (b#≤b# pf₁) = b#≤b# (≤-trans pf₀ pf₁)
  ≤-trans (b#≤b# pf₀) (0#≤1# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-trans (b#≤b# pf₀) (1#≤0# pf₁) = 1#≤0# (≤-<-trans-< pf₀ pf₁)
  ≤-trans (0#≤1# pf₀) (b#≤b# pf₁) = 0#≤1# (≤-trans pf₀ pf₁)
  ≤-trans (0#≤1# pf₀) (1#≤0# pf₁) = b#≤b# (≤-<-trans-≤ pf₀ pf₁)
  ≤-trans (1#≤0# pf₀) (b#≤b# pf₁) = 1#≤0# (<-≤-trans-< pf₀ pf₁)
  ≤-trans (1#≤0# pf₀) (0#≤1# pf₁) = b#≤b# (<-≤-trans-≤ pf₀ pf₁)


<⇒≤ : ∀ {n} {x y : BitVector n} → x < y → x ≤ y
<⇒≤ (b#<b# pf) = b#≤b# (<⇒≤ pf)
<⇒≤ (0#<1# pf) = 0#≤1# pf
<⇒≤ (1#<0# pf) = 1#≤0# pf


≤⇒≡⊎< : ∀ {n} → {x y : BitVector n} → x ≤ y → x ≡ y ⊎ x < y
≤⇒≡⊎< []≤[] = inj₁ refl
≤⇒≡⊎< (b#≤b# pf) with ≤⇒≡⊎< pf
...                 | inj₁ refl = inj₁ refl
...                 | inj₂ x<y = inj₂ (b#<b# x<y)
≤⇒≡⊎< (0#≤1# pf) = inj₂ (0#<1# pf)
≤⇒≡⊎< (1#≤0# pf) = inj₂ (1#<0# pf)

helper≢ : ∀ {n} {x y} {xs ys : BitVector n} → ¬ xs < ys → xs ≢ ys → ¬ x ∷ xs < y ∷ ys
helper≢ xs≮ys xs≢ys (b#<b# pf) = xs≮ys pf
helper≢ xs≮ys xs≢ys (1#<0# pf) = xs≮ys pf
helper≢ xs≮ys xs≢ys (0#<1# pf) with ≤⇒≡⊎< pf
...                               | inj₁ x≡y = xs≢ys x≡y
...                               | inj₂ x<y = xs≮ys x<y

helper≡ : ∀ {n} {xs : BitVector n} → ¬ 1# ∷ xs < 0# ∷ xs
helper≡ (1#<0# pf) = <-irr pf

compare : ∀ {n} → Trichotomous _≡_ (_<_ {n})
compare [] [] = tri≈ (λ ()) refl (λ ())
compare (x ∷ xs) (y ∷ ys) with compare xs ys 
compare (0# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = tri< (b#<b# a)       (¬b ∘ cong tail) (helper≢ ¬c (¬b ∘ sym))
compare (0# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = tri< (0#<1# (<⇒≤ a)) (¬b ∘ cong tail) (helper≢ ¬c (¬b ∘ sym))
compare (1# ∷ xs) (0# ∷ ys) | tri< a ¬b ¬c = tri< (1#<0# a)       (¬b ∘ cong tail) (helper≢ ¬c (¬b ∘ sym))
compare (1# ∷ xs) (1# ∷ ys) | tri< a ¬b ¬c = tri< (b#<b# a)       (¬b ∘ cong tail) (helper≢ ¬c (¬b ∘ sym))
compare (0# ∷ xs) (0# ∷ ._) | tri≈ ¬a refl ¬c = tri≈ <-irr refl <-irr
compare (0# ∷ xs) (1# ∷ ._) | tri≈ ¬a refl ¬c = tri< (0#<1# (≤-refl refl)) (λ ()) helper≡
compare (1# ∷ xs) (0# ∷ ._) | tri≈ ¬a refl ¬c = tri> helper≡ (λ ()) (0#<1# (≤-refl refl))
compare (1# ∷ xs) (1# ∷ ._) | tri≈ ¬a refl ¬c = tri≈ <-irr refl <-irr
compare (0# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = tri> (helper≢ ¬a ¬b) (¬b ∘ cong tail) (b#<b# c) 
compare (0# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = tri> (helper≢ ¬a ¬b) (λ ()) (1#<0# c)
compare (1# ∷ xs) (0# ∷ ys) | tri> ¬a ¬b c = tri> (helper≢ ¬a ¬b) (λ ()) (0#<1# (<⇒≤ c)) 
compare (1# ∷ xs) (1# ∷ ys) | tri> ¬a ¬b c = tri> (helper≢ ¬a ¬b) (¬b ∘ cong tail) (b#<b# c) 

≤-total : ∀ {n} → Total (_≤_ {n})
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


_≤?_ : ∀ {n} → Decidable (_≤_ {n})
x ≤? y with compare x y
...       | tri< a ¬b ¬c = yes (<⇒≤ a)
...       | tri≈ ¬a b ¬c = yes (≤-refl b)
...       | tri> ¬a ¬b c = no  helper
  where helper : ¬ x ≤ y
        helper x≤y with ≤⇒≡⊎< x≤y
        ...           | inj₁ x≡y = ¬b x≡y 
        ...           | inj₂ x<y = ¬a x<y

decTotalOrder : ∀ {n} → DecTotalOrder _ _ _
decTotalOrder {n} = record
  { Carrier         = BitVector n
  ; _≈_             = _≡_
  ; _≤_             = _≤_
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
      }
  }
