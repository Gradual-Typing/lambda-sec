module Types where

open import Data.Bool using (Bool) renaming (_≟_ to _≟ᵇ_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ₙ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

open import IFLabels public

data Base : Set where
  `ℕ : Base
  `𝔹 : Base
  Unit : Base
  Void : Base

rep : Base → Set
rep `ℕ = ℕ
rep `𝔹 = Bool
rep Unit = ⊤
rep Void = ⊥

data RawType : Set
data Type : Set

infix 10 `_
infix 7  _⟦_⟧⇒_
infix 6  _^_

data RawType where
  `_ : Base → RawType
  _⟦_⟧⇒_ : Type → Label → Type → RawType
  Ref : Type → RawType

data Type where
  _^_ : RawType → Label → Type

-- Examples:
_ : Type
_ = (` `ℕ ^ *) ⟦ ᴸ ⟧⇒ (` `𝔹 ^ ᴴ) ^ ᴸ

_ : Type
_ = Ref (` Void ^ *) ^ ᴴ

infix 5 _~_
infix 5 _≲_

-- Type consistency
data _~_ : Type → Type → Set where

  ~-ι : ∀ {ι ℓ₁ ℓ₂}
    → ℓ₁ ∼ ℓ₂
      --------------------
    → ` ι ^ ℓ₁  ~  ` ι ^ ℓ₂

  ~-Ref : ∀ {T₁ T₂ ℓ₁ ℓ₂}
    → ℓ₁ ∼ ℓ₂
    → T₁ ~ T₂
      ---------------------------
    → Ref T₁ ^ ℓ₁  ~  Ref T₂ ^ ℓ₂

  ~-⇒ : ∀ {S₁ S₂ T₁ T₂ pc₁ pc₂ ℓ₁ ℓ₂}
    → ℓ₁ ∼ ℓ₂
    → pc₁ ∼ pc₂
    → S₁ ~ T₁
    → S₂ ~ T₂
      -------------------------------------------
    → S₁ ⟦ pc₁ ⟧⇒ S₂ ^ ℓ₁  ~  T₁ ⟦ pc₂ ⟧⇒ T₂ ^ ℓ₂

-- Consistent subtyping
data _≲_ : Type → Type → Set where

  ≲-ι : ∀ {ι ℓ₁ ℓ₂}
    → ℓ₁ ≾ ℓ₂
      ------------------------
    → ` ι ^ ℓ₁  ≲  ` ι ^ ℓ₂

  ≲-Ref : ∀ {T₁ T₂ ℓ₁ ℓ₂}
    → ℓ₁ ≾ ℓ₂
    → T₁ ~ T₂
      --------------------------
    → Ref T₁ ^ ℓ₁  ≲  Ref T₂ ^ ℓ₂

  ≲-⇒ : ∀ {S₁ S₂ T₁ T₂ pc₁ pc₂ ℓ₁ ℓ₂}
    → ℓ₁ ≾ ℓ₂
    → pc₂ ≾ pc₁
    → T₁ ≲ S₁
    → S₂ ≲ T₂
      ----------------------------------------------
    → S₁ ⟦ pc₁ ⟧⇒ S₂ ^ ℓ₁  ≲  T₁ ⟦ pc₂ ⟧⇒ T₂ ^ ℓ₂
