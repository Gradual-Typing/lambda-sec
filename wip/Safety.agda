open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst; subst₂; trans)

open import Lemmas
open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Store
open import Interp
open import WellTypedness




𝒱-safe : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ}
  → (k : ℕ)
  → (pc₀ : ℒ)
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → Γ ∣ μ ⊢ₑ γ
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 γ M ⊢M μ pc₀ k ⦂ T
𝒱-safe 0 _ _ _ _ _ = ⊢ᵣtimeout

𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢tt = ⊢ᵣresult ⊢μ ⊢ᵥtt
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢true = ⊢ᵣresult ⊢μ ⊢ᵥtrue
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢false = ⊢ᵣresult ⊢μ ⊢ᵥfalse
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢label = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe {γ = γ} {M = (` x)} (suc k) pc₀ ⊢μ _ ⊢γ (⊢` eq) rewrite proj₂ (⊢γ→∃v ⊢γ eq) =
  ⊢ᵣresult ⊢μ (⊢γ→⊢v ⊢γ eq)

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) rewrite proj₂ (⊢γ→∃v ⊢γ eq) with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
--   : Goes to the M branch
𝒱-safe {γ = γ} {M = if `x M N} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true
  with 𝒱 γ M ⊢M μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢M  -- Case split on the evaluation of M
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  with (l̂ pc′) ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | yes _ with 𝓁̂₂ ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T⋎T′≡T″) | V-true | ⊢ᵥ-true | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | yes _ | yes _ with T ≲? T″
... | yes T≲T″ = ⊢castT′ T≲T″ ⊢μ′ ⊢vₘ
... | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | yes _ | no  oops = ⊥-elim (oops 𝓁̂≾𝓁̂⊔̂𝓁̂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-true | ⊢ᵥ-true | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
--   : Goes to the N branch
𝒱-safe {γ = γ} {M = if `x M N} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false
  with 𝒱 γ N ⊢N μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢N  -- Case split on the evaluation of N
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  with (l̂ pc′) ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | yes _ with 𝓁̂₂′ ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T⋎T′≡T″) | V-false | ⊢ᵥ-false | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | yes _ | yes _ with T′ ≲? T″
... | yes T′≲T″ = ⊢castT′ T′≲T″ ⊢μ′ ⊢vₙ
... | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | yes _ | no  oops = ⊥-elim (oops 𝓁̂≾𝓁̂′⊔̂𝓁̂)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _) | V-false | ⊢ᵥ-false | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error

-- Start with empty env and store.
-- type-safety : ∀ {T M 𝓁̂₁ 𝓁̂₂ pc₀}
--   → (k : ℕ)
--   → (⊢M : [] [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
--     ----------------------------
--   → ⊢ᵣ 𝒱 [] M ⊢M [] pc₀ k ⦂ T
-- type-safety k ⊢M = 𝒱-safe k ⊢ₛ∅ ∉domₙ∅ ⊢ₑ∅ ⊢M
