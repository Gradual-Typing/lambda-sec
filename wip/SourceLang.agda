module SourceLang where

open import IFLabels public
open import Types public
open import Variables public


-- Defines the type system of the surface language.

-- Γ ; pc* ⊢ M ⦂ T
infix 4 _;_⊢G_

data _;_⊢G_ : Context → Label → Type → Set where

  `_ : ∀ {Γ pc A}
    → Γ ∋ A
      --------
    → Γ ; pc ⊢G A

  -- A value need to be annotated with static label
  $_^_ : ∀ {Γ pc ι ℓ}
    → rep ι
    → StaticLabel ℓ
      ----------------------
    → Γ ; pc ⊢G ` ι ^ ℓ

  ƛ_^_ : ∀ {Γ pc A B pc₀ ℓ}
    → Γ , A ; pc₀ ⊢G B
    → StaticLabel ℓ
      -------------------------------
    → Γ ; pc ⊢G A ⟦ pc₀ ⟧⇒ B ^ ℓ

  prot : ∀ {Γ pc τᴬ ℓᴬ ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⋎ ℓ ⊢G τᴬ ^ ℓᴬ
      -----------------------
    → Γ ; pc ⊢G τᴬ ^ (ℓᴬ ⋎ ℓ)

  _·_ : ∀ {Γ pc A A′ τᴮ ℓᴮ pc₀ ℓ}
    → Γ ; pc ⊢G A ⟦ pc₀ ⟧⇒ (τᴮ ^ ℓᴮ) ^ ℓ
    → Γ ; pc ⊢G A′
    -- Note that ℓ₁ ⋎ ℓ₂ ≾ ℓ ⌿→ ℓ₁ ≾ ℓ ∧ ℓ₂ ≾ ℓ
    → {pc ≾ pc₀} → {ℓ ≾ pc₀}
    → {A′ ≲ A}
      --------------------------
    -- We snap label ℓ on the result
    → Γ ; pc ⊢G τᴮ ^ (ℓᴮ ⋎ ℓ)

  ref : ∀ {Γ pc τᴬ ℓᴬ ℓ}
    → StaticLabel ℓ
    → Γ ; pc ⊢G τᴬ ^ ℓᴬ
    → {pc ≾ ℓᴬ}
      ----------------------------
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ

  _:=_ : ∀ {Γ pc τᴬ ℓᴬ A′ ℓ}
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ
    → Γ ; pc ⊢G A′
    -- The NSU check here is analogous to the check of function application
    → {pc ≾ ℓᴬ} → {ℓ ≾ ℓᴬ}
    → {A′ ≲ τᴬ ^ ℓᴬ}
      -------------------
    -- `Unit` never leaks information so it's fine to be low security.
    → Γ ; pc ⊢G ` Unit ^ ᴸ

  !_ : ∀ {Γ pc τᴬ ℓᴬ ℓ}
    → Γ ; pc ⊢G Ref (τᴬ ^ ℓᴬ) ^ ℓ
      -----------------------------
    → Γ ; pc ⊢G τᴬ ^ (ℓᴬ ⋎ ℓ)

-- Examples:
--   TODO add more examples here
_ : ∅ ; ᴸ ⊢G ` `ℕ ^ ᴴ
_ = $ 42 ^ ᴴ
