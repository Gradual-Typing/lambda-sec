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

  -- A value need to be annotated with static label
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

  prot : ∀ {Γ τᴬ ℓᴬ pc ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⋎ ℓ ⊢G τᴬ ^ ℓᴬ
      -----------------------
    → Γ ; pc ⊢G τᴬ ^ (ℓᴬ ⋎ ℓ)

  _·_ : ∀ {Γ A A′ τᴮ ℓᴮ pc pc₀ ℓ}
    → Γ ; pc ⊢G A ⟦ pc₀ ⟧⇒ (τᴮ ^ ℓᴮ) ^ ℓ
    → Γ ; pc ⊢G A′
    -- Note that ℓ₁ ⋎ ℓ₂ ≾ ℓ ⌿→ ℓ₁ ≾ ℓ ∧ ℓ₂ ≾ ℓ
    → {pc ≾ pc₀} → {ℓ ≾ pc₀}
    → {A′ ≲ A}
      --------------------------
    -- We snap label ℓ on the result
    → Γ ; pc ⊢G τᴮ ^ (ℓᴮ ⋎ ℓ)

  ref : ∀ {Γ τᴬ ℓᴬ pc ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⊢G τᴬ ^ ℓᴬ
    → {pc ≾ ℓᴬ}
      ----------------------------
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ

  _:=_ : ∀ {Γ τᴬ ℓᴬ A′ pc ℓ}
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ
    → Γ ; pc ⊢G A′
    -- The NSU check here is analogous to the check of function application
    → {pc ≾ ℓᴬ} → {ℓ ≾ ℓᴬ}
    → {A′ ≲ τᴬ ^ ℓᴬ}
      -------------------
    -- `Unit` never leaks information so it's fine to be low security.
    → Γ ; pc ⊢G ` Unit ^ ᴸ

  !_ : ∀ {Γ τᴬ ℓᴬ pc ℓ}
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ
      -----------------------------
    → Γ ; pc ⊢G τᴬ ^ (ℓᴬ ⋎ ℓ)

-- Examples:
--   TODO add more examples here
_ : ∅ ; ᴸ ⊢G ` `ℕ ^ ᴴ
_ = $ 42 ^ ᴴ
