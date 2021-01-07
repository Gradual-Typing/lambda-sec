module IFLabels where

open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary using (¬_; Dec; yes; no)

data Label : Set where
  * : Label
  ᴴ : Label
  ᴸ : Label

data StaticLabel : Label → Set where
  ᴴ : StaticLabel ᴴ
  ᴸ : StaticLabel ᴸ

-- Gradual join
_⋎_ : Label → Label → Label
ᴸ ⋎ ᴴ = ᴴ
ᴸ ⋎ ᴸ = ᴸ
ᴸ ⋎ * = *
ᴴ ⋎ _ = ᴴ
* ⋎ _ = *

-- Gradual meet
_⋏_ : Label → Label → Label
ᴴ ⋏ ᴸ = ᴸ
ᴴ ⋏ ᴴ = ᴴ
ᴴ ⋏ * = *
ᴸ ⋏ _ = ᴸ
* ⋏ _ = *

infix 5 _∼_
infix 5 _≼_
infix 5 _≾_

data _≼_ : ∀ {ℓ₁ ℓ₂} → StaticLabel ℓ₁ → StaticLabel ℓ₂ → Set where
  ≼-ll : ᴸ ≼ ᴸ
  ≼-hh : ᴴ ≼ ᴴ
  ≼-lh : ᴸ ≼ ᴴ

-- Consistency
data _∼_ : Label → Label → Set where
  ∼-*₁ : ∀ {ℓ} → * ∼ ℓ
  ∼-*₂ : ∀ {ℓ} → ℓ ∼ *
  ∼-ll : ᴸ ∼ ᴸ
  ∼-hh : ᴴ ∼ ᴴ

-- Consistent subtyping of labels
data _≾_ : Label → Label → Set where
  ≾-*₁ : ∀ {ℓ} → * ≾ ℓ

  ≾-*₂ : ∀ {ℓ} → ℓ ≾ *

  ≾-static : ∀ {ℓ₁ ℓ₂} {s₁ : StaticLabel ℓ₁} {s₂ : StaticLabel ℓ₂}
    → s₁ ≼ s₂
      ----------
    → ℓ₁ ≾ ℓ₂


-- Helpers
eq-unk : ∀ (ℓ : Label) → Dec (ℓ ≡ *)
eq-unk * = yes refl
eq-unk ᴴ = no (λ ())
eq-unk ᴸ = no (λ ())

Refl≾ : ∀ {ℓ} → ℓ ≾ ℓ
Refl≾ {ℓ = *} = ≾-*₁
Refl≾ {ℓ = ᴴ} = ≾-static ≼-hh
Refl≾ {ℓ = ᴸ} = ≾-static ≼-ll
