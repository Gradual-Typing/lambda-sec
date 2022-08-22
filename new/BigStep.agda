module BigStep where

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC

infix 2 _∣_∣_⇓_∣_∣_

{- only consider evaluation to values -}
data _∣_∣_⇓_∣_∣_ : Term → Heap → StaticLabel → (V : Term) → Value V → Heap → Set where

  ⇓-val : ∀ {μ pc V v}
      --------------------------- Value
    → V ∣ μ ∣ pc ⇓ V ∣ v ∣ μ

  ⇓-app : ∀ {μ μ₁ μ₂ μ₃ pc pc′ L M N V W v w A ℓ}
    → L       ∣ μ  ∣ pc     ⇓ ƛ[ pc′ ] A ˙ N of ℓ ∣ V-ƛ ∣ μ₁
    → M       ∣ μ₁ ∣ pc     ⇓ V ∣ v ∣ μ₂
    → N [ V ] ∣ μ₂ ∣ pc ⋎ ℓ ⇓ W ∣ w ∣ μ₃
      ------------------------------------------------------------- Application
    → L · M ∣ μ ∣ pc ⇓ stamp-val W w ℓ ∣ stamp-val-value w ∣ μ₃



