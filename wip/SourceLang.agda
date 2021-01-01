module SourceLang where

open import IFLabels public
open import Types public
open import Variables public


-- Defines the type system of the surface language.

-- Γ ; pc* ⊢ M ⦂ T
infix 4 _;_⊢G_

data _;_⊢G_ : Context → Label → Type → Set where

  `_ : ∀ {Γ A pc}
    → Γ ∋ A
      --------
    → Γ ; pc ⊢G A

  $_^_ : ∀ {Γ ι pc ℓ}
    → rep ι
    → StaticLabel ℓ
      ----------------------
    → Γ ; pc ⊢G ` ι ^ ℓ

  ƛ_^_ : ∀ {Γ A B pc pc₀ ℓ}
    → Γ , A ; pc₀ ⊢G B
    → StaticLabel ℓ
      -------------------------------
    → Γ ; pc ⊢G A ⟦ pc₀ ⟧⇒ B ^ ℓ

  prot : ∀ {Γ τ ℓ₀ pc ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⋎ ℓ ⊢G τ ^ ℓ₀
      -----------------------
    → Γ ; pc ⊢G τ ^ (ℓ₀ ⋎ ℓ)

  _·_ : ∀ {Γ A A′ τᴮ ℓᴮ pc₀ pc ℓ}
    → Γ ; pc ⊢G A ⟦ pc₀ ⟧⇒ (τᴮ ^ ℓᴮ) ^ ℓ
    → Γ ; pc ⊢G A′
    → {pc ≾ pc₀} → {ℓ ≾ pc₀}
    → {A′ ≲ A}
      --------------------------
    → Γ ; pc ⊢G τᴮ ^ (ℓᴮ ⋎ ℓ)

  ref : ∀ {Γ τᴬ ℓᴬ pc ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⊢G τᴬ ^ ℓᴬ
    → {pc ≾ ℓᴬ}
      ----------------------------
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ

  -- _:=_ : ∀ {}

-- Examples:
--   TODO add more examples here
_ : ∅ ; ᴸ ⊢G ` `ℕ ^ ᴴ
_ = $ 42 ^ ᴴ
