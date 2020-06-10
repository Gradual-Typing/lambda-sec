open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)

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

-- Progress and preservation
type-safety : ∀ {T M 𝓁̂₁ 𝓁̂₂ pc₀ k}
  → (⊢M : [] [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → ⊢ᵣ 𝒱 [] M ⊢M [] pc₀ k ⦂ T
