module TargetLang where

open import Types public
open import Variables public
open import SourceLang public

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
      ------------------------
    → Γ ; Σ ; pc ⊢ τᴬ ^ (ℓᴬ ⋎ ℓ)

  _·_ : ∀ {Γ Σ pc A τᴮ ℓᴮ ℓ}
    → Γ ; Σ ; pc ⊢ A ⟦ pc ⟧⇒ (τᴮ ^ ℓᴮ) ^ ℓ
    → Γ ; Σ ; pc ⊢ A
    → {ℓ ≾ pc}
      --------------------------
    → Γ ; Σ ; pc ⊢ τᴮ ^ (ℓᴮ ⋎ ℓ)

data Value where

  V-const : ∀ {Γ Σ pc ι} {k : rep ι} {ℓ} {s : StaticLabel ℓ}
    → Value {Γ} {Σ} {pc} ($ k ^ s)

  V-ƛ : ∀ {Γ Σ pc A B pc₀ ℓ} {N : Γ , A ; Σ ; pc₀ ⊢ B} {s : StaticLabel ℓ}
    → Value {pc = pc} (ƛ N ^ s)

  -- TODO: add a case for wrapped value here
