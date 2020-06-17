open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂; subst; subst₂)

open import StaticsLIO
open import Store
open import Interp

infix 4 _∣_⊢ₑ_
infix 4 _⊢ᵥ_⦂_
infix 4 _⊢ₛ_


-- Well-typed environment γ under context Γ
data _∣_⊢ₑ_ : Context → Store → Env → Set
-- Well-typed value under store μ
--   NOTE: Since μ contains type information, it doubles as store typing context Σ here.
data _⊢ᵥ_⦂_ : Store → Value → 𝕋 → Set
-- Well-typed store
data _⊢ₛ_ : Store → Store → Set


data _∣_⊢ₑ_ where

  ⊢ₑ∅ : ∀ {μ}
      -------------
    → [] ∣ μ ⊢ₑ []

  ⊢ₑ∷ : ∀ {Γ μ γ v T}
    → μ ⊢ᵥ v ⦂ T
    → Γ ∣ μ ⊢ₑ γ
      --------------
    → T ∷ Γ ∣ μ ⊢ₑ v ∷ γ


data _⊢ᵥ_⦂_ where

  ⊢ᵥtt : ∀ {μ}
      --------- Unit
    → μ ⊢ᵥ V-tt ⦂ `⊤

  ⊢ᵥtrue : ∀ {μ}
      ------------ True
    → μ ⊢ᵥ V-true ⦂ `𝔹

  ⊢ᵥfalse : ∀ {μ}
      ------------- False
    → μ ⊢ᵥ V-false ⦂ `𝔹

  ⊢ᵥlabel : ∀ {μ 𝓁}
      ------------------ Label
    → μ ⊢ᵥ V-label 𝓁 ⦂ `ℒ

  ⊢ᵥclos : ∀ {Δ μ γ T S M 𝓁̂₁ 𝓁̂₂}
    → Δ ∣ μ ⊢ₑ γ
    → (⊢M : T ∷ Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ S)
      ---------------------------------------------- Closure
    → μ ⊢ᵥ V-clos < M , γ , ⊢M > ⦂ T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S

  ⊢ᵥproxy : ∀ {μ S T S′ T′ v 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′}
    → μ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T
      --------------------------------------------------------------------------------------- Proxy
    → μ ⊢ᵥ V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′ v ⦂ S′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T′

  ⊢ᵥref : ∀ {μ T n 𝓁₁ 𝓁₂ v}
    → lookup μ ⟨ n , ⟨ 𝓁₁ , 𝓁₂ ⟩ ⟩ ≡ just ⟨ T , v ⟩
      ----------------------------------- Ref
    → μ ⊢ᵥ V-ref ⟨ n , ⟨ 𝓁₁ , 𝓁₂ ⟩ ⟩ ⦂ Ref (l̂ 𝓁₂) T

  ⊢ᵥlab : ∀ {μ T v 𝓁}
    → μ ⊢ᵥ v ⦂ T
      --------------------------- Labeled
    → μ ⊢ᵥ V-lab 𝓁 v ⦂ Lab (l̂ 𝓁) T


data _⊢ₛ_ where

  ⊢ₛ∅ : ∀ {μ}
    → μ ⊢ₛ []

  ⊢ₛ∷ : ∀ {μ σ v T} {loc : Location}
    → μ ⊢ᵥ v ⦂ T
    → μ ⊢ₛ σ
      --------------------------
    → μ ⊢ₛ (loc ↦ ⟨ T , v ⟩) ∷ σ


-- Well-typed result
infix 4 ⊢ᵣ_⦂_

data ⊢ᵣ_⦂_ : Result Conf → 𝕋 → Set where

  ⊢ᵣresult : ∀ {μ T v pc}
    → μ ⊢ₛ μ
    → μ ⊢ᵥ v ⦂ T
      ---------------------------------
    → ⊢ᵣ result ⟨ μ , ⟨ v , pc ⟩ ⟩ ⦂ T

  -- Cast error, NSU check failure and diverging are always well-typed under any T ∈ 𝕋
  --   NOTE: *stuck* is ruled out here !
  ⊢ᵣcast-error : ∀ {T}
    → ⊢ᵣ error castError ⦂ T

  ⊢ᵣnsu-error : ∀ {T}
    → ⊢ᵣ error NSUError ⦂ T

  ⊢ᵣtimeout : ∀ {T}
    → ⊢ᵣ timeout ⦂ T


just-≡-inv : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-≡-inv {X} {x} {y}  refl = refl

-- Env lookup is safe
nth-safe : ∀ {Γ μ γ T v x}
  → Γ ∣ μ ⊢ₑ γ
  → nth Γ x ≡ just T
  → nth γ x ≡ just v
    ------------------
  → μ ⊢ᵥ v ⦂ T
nth-safe {μ = μ} {x = 0} (⊢ₑ∷ ⊢v₀ _) eq₁ eq₂ =
  let T₀≡T = just-≡-inv eq₁ in
  let v₀≡v = just-≡-inv eq₂ in
    subst₂ (λ □₁ □₂ → μ ⊢ᵥ □₁ ⦂ □₂) v₀≡v T₀≡T ⊢v₀
nth-safe {x = suc x} (⊢ₑ∷ _ Γμ⊢γ) eq₁ eq₂ = nth-safe Γμ⊢γ eq₁ eq₂

𝒱-safe : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ pc₀ k}
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 γ M ⊢M μ pc₀ k ⦂ T
