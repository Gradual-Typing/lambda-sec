open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; subst; subst₂)

open import StaticsLIO
open import Value
open import Interp



-- Well-typed result
infix 4 ⊢ᵣ_⦂_

data ⊢ᵣ_⦂_ : Result Conf → 𝕋 → Set where

  ⊢ᵣresult : ∀ {T v m pc}
    → ⊢ᵥ v ⦂ T
      ---------------------------------
    → ⊢ᵣ result ⟨ m , ⟨ v , pc ⟩ ⟩ ⦂ T

  -- Error and diverging are always well-typed under any T ∈ 𝕋
  ⊢ᵣerror : ∀ {T err}
    → ⊢ᵣ error err ⦂ T

  ⊢ᵣtimeout : ∀ {T}
    → ⊢ᵣ timeout ⦂ T

just-≡-inv : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-≡-inv {X} {x} {y}  refl = refl

-- Lookup is safe
lookup-safe : ∀ {Γ γ T v x}
  → γ ⊨ Γ
  → nth Γ x ≡ just T
  → nth γ x ≡ just v
  → ⊢ᵥ v ⦂ T
lookup-safe {T = T} {v} {0} (⊨-∷ {v = v₀} {T₀} ⊢v₀ γ⊨Γ) eq₁ eq₂ =
  let T₀≡T = just-≡-inv eq₁ in
  let v₀≡v = just-≡-inv eq₂ in subst₂ (λ □₁ □₂ → ⊢ᵥ □₁ ⦂ □₂) v₀≡v T₀≡T ⊢v₀
lookup-safe {T = T} {v} {suc x} (⊨-∷ {v = v₀} {T₀} ⊢v₀ γ⊨Γ) eq₁ eq₂ = lookup-safe γ⊨Γ eq₁ eq₂

𝒱-safe : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ m pc₀ k}
  → γ ⊨ Γ
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → ⊢ᵣ 𝒱 γ M ⊢M m pc₀ k ⦂ T
