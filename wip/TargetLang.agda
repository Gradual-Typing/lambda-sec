module TargetLang where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; sym; cong)

open import Types public
open import Variables public
open import BlameLabels public
open import SourceLang public

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ (S T : Type) → BlameLabel → S ≲ T → Cast S ⇒ T

data Inert : ∀ {S T} → Cast S ⇒ T → Set where
  I-inj : ∀ {ι ℓ} → ℓ ≢ * → (c : Cast (` ι ^ ℓ) ⇒ (` ι ^ *)) → Inert c
  I-fun : ∀ {A₁ B₁ pc₁ A₂ B₂ pc₂ ℓ₁ ℓ₂} → (c : Cast (A₁ ⟦ pc₁ ⟧⇒ B₁ ^ ℓ₁) ⇒ (A₂ ⟦ pc₂ ⟧⇒ B₂ ^ ℓ₂)) → Inert c
  I-ref : ∀ {A₁ A₂ ℓ₁ ℓ₂} → (c : Cast (Ref A₁ ^ ℓ₁) ⇒ (Ref A₂ ^ ℓ₂)) → Inert c

data Active : ∀ {S T} → Cast S ⇒ T → Set where
  -- ⋆ ⇒ ⋆ or projection
  A-from* : ∀ {ι ℓ} → (c : Cast (` ι ^ *) ⇒ (` ι ^ ℓ)) → Active c
  A-sub : ∀ {ι ℓ₁ ℓ₂} {s₁ : StaticLabel ℓ₁} {s₂ : StaticLabel ℓ₂} → s₁ ≼ s₂ → (c : Cast (` ι ^ ℓ₁) ⇒ (` ι ^ ℓ₂)) → Active c

ActiveOrInert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
ActiveOrInert (cast (` A ^ ℓ₁) (` .A ^ ℓ₂) p (≲-ι cs)) with eq-unk ℓ₁ | eq-unk ℓ₂
... | yes eq1 | yes eq2 rewrite eq1 | eq2 = inj₁ (A-from* _)
... | yes eq | no neq rewrite eq = inj₁ (A-from* _)
... | no neq | yes eq rewrite eq = inj₂ (I-inj neq _)
... | no neq1 | no neq2 with cs
...   | ≾-*₁ = contradiction refl neq1
...   | ≾-*₂ = inj₂ (I-inj (λ _ → neq2 refl) _)
...   | ≾-static sub = inj₁ (A-sub sub _)
ActiveOrInert (cast (A₁ ⟦ pc₁ ⟧⇒ B₁ ^ ℓ₁) (A₂ ⟦ pc₂ ⟧⇒ B₂ ^ ℓ₂) p cs) = inj₂ (I-fun _)
ActiveOrInert (cast (Ref A ^ ℓ₁) (Ref B ^ ℓ₂) p cs) = inj₂ (I-ref _)

ActiveNotInert : ∀ {A B} {c : Cast A ⇒ B} → Active c → ¬ Inert c
ActiveNotInert (A-from* _) (I-inj neq _) = contradiction refl neq
ActiveNotInert (A-sub () _) (I-inj _ _)

-- Γ ; Σ ; pc ⊢ M ⦂ A
infix 4 _;_;_⊢_

data _;_;_⊢_ : Context → Context → Label → Type → Set

data Value : ∀ {Γ μ pc A} → Γ ; μ ; pc ⊢ A → Set

data _;_;_⊢_ where

  `_ : ∀ {Γ Σ pc A}
    → Γ ∋ A
      ---------------
    → Γ ; Σ ; pc ⊢ A

  _^_ : ∀ {Γ Σ pc T ℓ}
    → Σ ∋ T
    → StaticLabel ℓ
      -------------------
    → Γ ; Σ ; pc ⊢ Ref T ^ ℓ

  $_^_ : ∀ {Γ Σ pc ι ℓ}
    → rep ι
    → StaticLabel ℓ
      ----------------------
    → Γ ; Σ ; pc ⊢ ` ι ^ ℓ

  ƛ_^_ : ∀ {Γ Σ pc A B pc₀ ℓ}
    → Γ , A ; Σ ; pc₀ ⊢ B
    → StaticLabel ℓ
      -------------------------------
    → Γ ; Σ ; pc ⊢ A ⟦ pc₀ ⟧⇒ B ^ ℓ

  prot : ∀ {Γ Σ pc τᴬ ℓᴬ ℓ}
    → StaticLabel ℓ
    → Γ ; Σ ; pc ⋎ ℓ ⊢ τᴬ ^ ℓᴬ
      ---------------------------
    → Γ ; Σ ; pc ⊢ τᴬ ^ (ℓᴬ ⋎ ℓ)

  _·_ : ∀ {Γ Σ pc A τᴮ ℓᴮ pc₀ ℓ}
    → Γ ; Σ ; pc ⊢ A ⟦ pc₀ ⟧⇒ (τᴮ ^ ℓᴮ) ^ ℓ
    → Γ ; Σ ; pc ⊢ A
    → {pc ≾ pc₀} → {ℓ ≾ pc₀}
      --------------------------
    → Γ ; Σ ; pc ⊢ τᴮ ^ (ℓᴮ ⋎ ℓ)

  ref : ∀ {Γ Σ pc τᴬ ℓᴬ ℓ}
    → StaticLabel ℓ
    → Γ ; Σ ; pc ⊢ τᴬ ^ ℓᴬ
    → {pc ≾ ℓᴬ}
      -------------------------------
    → Γ ; Σ ; pc ⊢ Ref (τᴬ ^ ℓᴬ) ^ ℓ

  _:=_ : ∀ {Γ Σ pc τᴬ ℓᴬ ℓ}
    → Γ ; Σ ; pc ⊢ Ref (τᴬ ^ ℓᴬ) ^ ℓ
    → Γ ; Σ ; pc ⊢ τᴬ ^ ℓᴬ
    → {pc ≾ ℓᴬ} → {ℓ ≾ ℓᴬ}
      -------------------------
    → Γ ; Σ ; pc ⊢ ` Unit ^ ᴸ

  !_ : ∀ {Γ Σ pc τᴬ ℓᴬ ℓ}
    → Γ ; Σ ; pc ⊢ Ref (τᴬ ^ ℓᴬ) ^ ℓ
      -----------------------------
    → Γ ; Σ ; pc ⊢ τᴬ ^ (ℓᴬ ⋎ ℓ)

  _⟨_⟩ : ∀ {Γ Σ pc A B}
    → Γ ; Σ ; pc ⊢ A
    → Cast A ⇒ B
      ------------------
    → Γ ; Σ ; pc ⊢ B

  blame : ∀ {Γ Σ pc A}
    → BlameLabel
      -----------------
    → Γ ; Σ ; pc ⊢ A

data Value where

  V-const : ∀ {Γ Σ pc ι} {k : rep ι} {ℓ} {s : StaticLabel ℓ}
    → Value {Γ} {Σ} {pc} ($ k ^ s)

  V-ƛ : ∀ {Γ Σ pc A B pc₀ ℓ} {N : Γ , A ; Σ ; pc₀ ⊢ B} {s : StaticLabel ℓ}
    → Value {pc = pc} (ƛ N ^ s)

  V-cast : ∀ {Γ Σ pc A B} {V : Γ ; Σ ; pc ⊢ A} {c : Cast A ⇒ B}
    → Value V → Inert c
      -------------------
    → Value (V ⟨ c ⟩)
