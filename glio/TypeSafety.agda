open import Data.Nat using (ℕ)
open import Data.List using ([])

open import StaticsGLIO
open import Interp
open import WellTypedness
open import InterpSafe




-- Start with empty env and store.
type-safety : ∀ {T M ℓ̂₁ ℓ̂₂}
  → (k : ℕ)
  → (pc₀ : ℒ)
  → (⊢M : [] [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 [] M ⊢M [] pc₀ k ⦂ T
type-safety k pc₀ ⊢M = 𝒱-safe k pc₀ ⊢ₛ∅ ∉domₙ∅ ⊢ₑ∅ ⊢M
