module InterpSafe where

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
open import CastStateIdem

-- Well-formedness of heap w.r.t address
data WFaddr : Result Conf → Set where

  WFtimeout : WFaddr timeout

  WFerror : ∀ {err} → WFaddr (error err)

  WFresult : ∀ {μ v pc}
    → length μ ∉domₙ μ
    → WFaddr (result ⟨ μ , v , pc ⟩)

data WTenv : Result Conf → Context → Env → Set where

  WTenv-timeout : ∀ {Γ γ} → WTenv timeout Γ γ

  WTenv-error : ∀ {Γ γ err} → WTenv (error err) Γ γ

  WTenv-result : ∀ {Γ γ μ v pc}
    → Γ ∣ μ ⊢ₑ γ
    → WTenv (result ⟨ μ , v , pc ⟩) Γ γ



𝒱-pres-WFaddr : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ pc k}
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → length μ ∉domₙ μ
  → WFaddr (𝒱 γ M ⊢M μ pc k)

𝒱-pres-⊢ₑ : ∀ {Γ Δ γ ρ T M 𝓁̂₁ 𝓁̂₂ μ pc k}
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → Δ ∣ μ ⊢ₑ ρ
  → length μ ∉domₙ μ
  → WTenv (𝒱 γ M ⊢M μ pc k) Δ ρ

𝒱-safe : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ}
  → (k : ℕ)
  → (pc₀ : ℒ)
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → Γ ∣ μ ⊢ₑ γ
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 γ M ⊢M μ pc₀ k ⦂ T

apply-safe : ∀ {γ S T 𝓁̂₁ 𝓁̂₂ v w μ pc k}
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → μ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T
  → μ ⊢ᵥ w ⦂ S
  → ⊢ᵣ apply γ v w μ pc k ⦂ T

apply-pres-WFaddr : ∀ {γ S T 𝓁̂₁ 𝓁̂₂ v w μ pc k}
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → μ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T
  → μ ⊢ᵥ w ⦂ S
  → WFaddr (apply γ v w μ pc k)
apply-pres-WFaddr {μ = μ} {pc} {k} ⊢μ fresh (⊢ᵥclos {Δ} {γ = ρ} ⊢ρ ⊢N) ⊢w =
  𝒱-pres-WFaddr {pc = pc} {k} ⊢N ⊢μ (⊢ₑ∷ ⊢w ⊢ρ) fresh
apply-pres-WFaddr {γ} {w = w} {μ} {pc} {k} ⊢μ fresh (⊢ᵥproxy {S = S} {T} {S′} {T′} {v} {𝓁̂₁} {𝓁̂₂} {𝓁̂₁′} {𝓁̂₂′} {𝓁̂₁′≾𝓁̂₁ = 𝓁̂₁′≾𝓁̂₁} {𝓁̂₂≾𝓁̂₂′} ⊢v) ⊢w
  with castT μ pc S′ S w | ⊢castT {pc = pc} {S′} {S} ⊢μ ⊢w | castT-state-idem {μ} {pc} {S′} {S} ⊢w
... | timeout | _ | _ = WFtimeout
... | error NSUError | _ | _ = WFerror
... | error castError | _ | _ = WFerror
... | result ⟨ μ₁ , w′ , pc₁ ⟩ | ⊢ᵣresult ⊢μ₁ ⊢w′ | ▹result μ≡μ₁ _
  with castL μ₁ pc₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁ ⊢μ₁ | castL-state-idem {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁
...   | timeout | _ | _ = WFtimeout
...   | error NSUError | _ | _ = WFerror
...   | error castError | _ | _ = WFerror
...   | result ⟨ μ₂ , _ , pc₂ ⟩ | ⊢ᵣresult ⊢μ₂ _ | ▹result μ₁≡μ₂ _
  with apply γ v w′ μ₂ pc₂ k | apply-safe {γ} {pc = pc₂} {k} ⊢μ₂ freshμ₂ μ₂⊢v μ₂⊢w′ | apply-pres-WFaddr {γ} {pc = pc₂} {k} ⊢μ₂ freshμ₂ μ₂⊢v μ₂⊢w′
  where
  freshμ₂ = subst (λ □ → length □ ∉domₙ □) (trans μ≡μ₁ μ₁≡μ₂) fresh
  μ₂⊢v = subst (λ □ → □ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T) (trans μ≡μ₁ μ₁≡μ₂) ⊢v
  μ₂⊢w′ = subst (λ □ → □ ⊢ᵥ w′ ⦂ S) μ₁≡μ₂ ⊢w′
...     | timeout | _ | _ = WFtimeout
...     | error NSUError | _ | _ = WFerror
...     | error castError | _ | _ = WFerror
...     | result ⟨ μ₃ , v₁ , pc₃ ⟩ | ⊢ᵣresult ⊢μ₃ ⊢v₁ | WFresult fresh′
  with castL μ₃ pc₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′ | ⊢castL {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′ ⊢μ₃ | castL-state-idem {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′
...       | timeout | _ | _ = WFtimeout
...       | error NSUError | _ | _ = WFerror
...       | error castError | _ | _ = WFerror
...       | result ⟨ μ₄ , _ , pc₄ ⟩ | ⊢ᵣresult ⊢μ₄ _ | ▹result μ₃≡μ₄ _
  with castT μ₄ pc₄ T T′ v₁ | ⊢castT {pc = pc₄} {T} {T′} ⊢μ₄ μ₄⊢v₁ | castT-state-idem {μ₄} {pc₄} {T} {T′} μ₄⊢v₁
  where
  μ₄⊢v₁ = subst (λ □ → □ ⊢ᵥ v₁ ⦂ T) μ₃≡μ₄ ⊢v₁
...         | timeout | _ | _ = WFtimeout
...         | error NSUError | _ | _ = WFerror
...         | error castError | _ | _ = WFerror
...         | result ⟨ μ₄′ , _ , _ ⟩ | _ | ▹result μ₄≡μ₄′ _ rewrite (sym μ₄≡μ₄′) | (sym μ₃≡μ₄) = WFresult fresh′

apply-pres-⊢ₑ : ∀ {Δ γ ρ S T 𝓁̂₁ 𝓁̂₂ v w μ pc k}
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → μ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T
  → μ ⊢ᵥ w ⦂ S
  → Δ ∣ μ ⊢ₑ ρ
  → WTenv (apply γ v w μ pc k) Δ ρ
apply-pres-⊢ₑ {Δ} {γ} {ρ} {μ = μ} {pc} {k} ⊢μ fresh (⊢ᵥclos {Γ} {γ = γ′} ⊢γ′ ⊢N) ⊢w ⊢ρ =
  𝒱-pres-⊢ₑ {pc = pc} {k} ⊢N ⊢μ (⊢ₑ∷ ⊢w ⊢γ′) ⊢ρ fresh

apply-pres-⊢ₑ {Δ} {γ} {ρ} {w = w} {μ} {pc} {k} ⊢μ fresh (⊢ᵥproxy {S = S} {T} {S′} {T′} {v} {𝓁̂₁} {𝓁̂₂} {𝓁̂₁′} {𝓁̂₂′} {𝓁̂₁′≾𝓁̂₁ = 𝓁̂₁′≾𝓁̂₁} {𝓁̂₂≾𝓁̂₂′} ⊢v) ⊢w ⊢ρ
  with castT μ pc S′ S w | ⊢castT {pc = pc} {S′} {S} ⊢μ ⊢w | castT-state-idem {μ} {pc} {S′} {S} ⊢w
... | timeout | _ | _ = WTenv-timeout
... | error NSUError | _ | _ = WTenv-error
... | error castError | _ | _ = WTenv-error
... | result ⟨ μ₁ , w′ , pc₁ ⟩ | ⊢ᵣresult ⊢μ₁ ⊢w′ | ▹result μ≡μ₁ _
  with castL μ₁ pc₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁ ⊢μ₁ | castL-state-idem {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁
...   | timeout | _ | _ = WTenv-timeout
...   | error NSUError | _ | _ = WTenv-error
...   | error castError | _ | _ = WTenv-error
...   | result ⟨ μ₂ , _ , pc₂ ⟩ | ⊢ᵣresult ⊢μ₂ _ | ▹result μ₁≡μ₂ _
  with apply γ v w′ μ₂ pc₂ k | apply-safe {γ} {pc = pc₂} {k} ⊢μ₂ freshμ₂ μ₂⊢v μ₂⊢w′ | apply-pres-⊢ₑ {Δ} {γ} {ρ} {pc = pc₂} {k} ⊢μ₂ freshμ₂ μ₂⊢v μ₂⊢w′ μ₂⊢ρ
  where
  freshμ₂ = subst (λ □ → length □ ∉domₙ □) (trans μ≡μ₁ μ₁≡μ₂) fresh
  μ₂⊢v = subst (λ □ → □ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T) (trans μ≡μ₁ μ₁≡μ₂) ⊢v
  μ₂⊢w′ = subst (λ □ → □ ⊢ᵥ w′ ⦂ S) μ₁≡μ₂ ⊢w′
  μ₂⊢ρ = subst (λ □ → Δ ∣ □ ⊢ₑ ρ) (trans μ≡μ₁ μ₁≡μ₂) ⊢ρ
...     | timeout | _ | _ = WTenv-timeout
...     | error NSUError | _ | _ = WTenv-error
...     | error castError | _ | _ = WTenv-error
...     | result ⟨ μ₃ , v₁ , pc₃ ⟩ | ⊢ᵣresult ⊢μ₃ ⊢v₁ | WTenv-result μ₃⊢ρ
  with castL μ₃ pc₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′ | ⊢castL {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′ ⊢μ₃ | castL-state-idem {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′
...       | timeout | _ | _ = WTenv-timeout
...       | error NSUError | _ | _ = WTenv-error
...       | error castError | _ | _ = WTenv-error
...       | result ⟨ μ₄ , _ , pc₄ ⟩ | ⊢ᵣresult ⊢μ₄ _ | ▹result μ₃≡μ₄ _
  with castT μ₄ pc₄ T T′ v₁ | ⊢castT {pc = pc₄} {T} {T′} ⊢μ₄ μ₄⊢v₁ | castT-state-idem {μ₄} {pc₄} {T} {T′} μ₄⊢v₁
  where
  μ₄⊢v₁ = subst (λ □ → □ ⊢ᵥ v₁ ⦂ T) μ₃≡μ₄ ⊢v₁
...         | timeout | _ | _ = WTenv-timeout
...         | error NSUError | _ | _ = WTenv-error
...         | error castError | _ | _ = WTenv-error
...         | result ⟨ μ₄′ , _ , _ ⟩ | _ | ▹result μ₄≡μ₄′ _ rewrite (sym μ₄≡μ₄′) | (sym μ₃≡μ₄) = WTenv-result μ₃⊢ρ

𝒱-pres-⊢ₑ {k = 0} _ _ _ _ _ = WTenv-timeout

𝒱-pres-⊢ₑ {k = suc k} (⊢` eq) ⊢μ ⊢γ ⊢ρ fresh rewrite proj₂ (⊢γ→∃v ⊢γ eq) = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} ⊢tt ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ
𝒱-pres-⊢ₑ {k = suc k} ⊢true ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ
𝒱-pres-⊢ₑ {k = suc k} ⊢false ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {Γ} {Δ} {γ} {ρ} {μ = μ} {pc} {suc k} (⊢let {T = T} {T′} {M = M} {N} ⊢M ⊢N x) ⊢μ ⊢γ ⊢ρ fresh
  with 𝒱 {Γ} γ M ⊢M μ pc k | 𝒱-pres-WFaddr {Γ} {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ fresh | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M
     | 𝒱-pres-⊢ₑ {pc = pc} {k} ⊢M ⊢μ ⊢γ ⊢ρ fresh | 𝒱-pres-⊢ₑ {pc = pc} {k} ⊢M ⊢μ ⊢γ ⊢γ fresh
... | timeout | WFtimeout | ⊢ᵣtimeout | _ | _ = WTenv-timeout
... | error NSUError | WFerror | ⊢ᵣnsu-error | _ | _ = WTenv-error
... | error castError | WFerror | ⊢ᵣcast-error | _ | _ = WTenv-error
... | result ⟨ μ′ , v′ , pc′ ⟩ | WFresult fresh′ | ⊢ᵣresult ⊢μ′ ⊢v′ | WTenv-result μ′⊢ρ | WTenv-result μ′⊢γ
  with castT μ′ pc′ T′ T v′ | castT-state-idem {μ′} {pc′} {T′} {T} ⊢v′ | ⊢castT {μ′} {pc′} {T′} {T} ⊢μ′ ⊢v′
...   | result ⟨ μ″ , v″ , pc″ ⟩ | ▹result μ′≡μ″ _ | ⊢ᵣresult ⊢μ″ ⊢v″ =
  𝒱-pres-⊢ₑ {pc = pc″} {k} ⊢N ⊢μ″ (⊢ₑ∷ ⊢v″ μ″⊢γ) μ″⊢ρ freshμ″
  where
  μ″⊢ρ = subst (λ □ → Δ ∣ □ ⊢ₑ ρ) μ′≡μ″ μ′⊢ρ
  μ″⊢γ = subst (λ □ → Γ ∣ □ ⊢ₑ γ) μ′≡μ″ μ′⊢γ
  freshμ″ = subst (λ □ → length □ ∉domₙ □) μ′≡μ″ fresh′
...   | timeout | ▹timeout | ⊢ᵣtimeout = WTenv-timeout
...   | error NSUError | ▹error | ⊢ᵣnsu-error = WTenv-error
...   | error castError | ▹error | ⊢ᵣcast-error = WTenv-error

𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
𝒱-pres-⊢ₑ {γ = γ} {ρ} {μ = μ} {pc} {suc k} (⊢if {M = M} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh | V-true | ⊢ᵥtrue
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-⊢ₑ {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ ⊢ρ fresh
𝒱-pres-⊢ₑ {k = suc k} (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result _
  with castL μ′ pc′ 𝓁̂₂ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂⋎𝓁̂′ | ⊢castL {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂⋎𝓁̂′ ⊢μ′
     | castL-state-idem {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂⋎𝓁̂′
𝒱-pres-⊢ₑ {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  with castT μ″ pc″ T T″ vₘ | ⊢castT {μ″} {pc″} {T} {T″} ⊢μ″ ⊢vₘ″ | castT-state-idem {μ″} {pc″} {T} {T″} ⊢vₘ″
  where
  ⊢vₘ″ = subst (λ □ → □ ⊢ᵥ vₘ ⦂ T) μ′≡μ″ ⊢vₘ′
𝒱-pres-⊢ₑ {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result μ′⊢ρ
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | result ⟨ μ‴ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ″≡μ‴ _ rewrite sym (trans μ′≡μ″ μ″≡μ‴) = WTenv-result μ′⊢ρ
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WTenv-result _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WTenv-result _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WTenv-result _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | timeout | ⊢ᵣtimeout | _ = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | error NSUError | ⊢ᵣnsu-error | _ = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-true | ⊢ᵥtrue
  | error castError | ⊢ᵣcast-error | _ = WTenv-error
𝒱-pres-⊢ₑ {γ = γ} {ρ} {μ = μ} {pc} {suc k} (⊢if {N = N} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh | V-false | ⊢ᵥfalse
  with 𝒱 γ N ⊢N μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢N | 𝒱-pres-⊢ₑ {μ = μ} {pc} {k} ⊢N ⊢μ ⊢γ ⊢ρ fresh
𝒱-pres-⊢ₑ {k = suc k} (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WTenv-result _
  with castL μ′ pc′ 𝓁̂₂′ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂′⋎𝓁̂ | ⊢castL {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂′⋎𝓁̂ ⊢μ′
    | castL-state-idem {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂′⋎𝓁̂
𝒱-pres-⊢ₑ {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  with castT μ″ pc″ T′ T″ vₙ | ⊢castT {μ″} {pc″} {T′} {T″} ⊢μ″ ⊢vₙ′ | castT-state-idem {μ″} {pc″} {T′} {T″} ⊢vₙ′
  where
  ⊢vₙ′ = subst (λ □ → □ ⊢ᵥ vₙ ⦂ T′) μ′≡μ″ ⊢vₙ
𝒱-pres-⊢ₑ {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WTenv-result μ′⊢ρ
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | result ⟨ μ‴ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ″≡μ‴ _ rewrite sym (trans μ′≡μ″ μ″≡μ‴) = WTenv-result μ′⊢ρ
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WTenv-result _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | timeout | ⊢ᵣtimeout | _ = WTenv-timeout
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | error NSUError | ⊢ᵣnsu-error | _ = WTenv-error
𝒱-pres-⊢ₑ {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ ⊢ρ fresh
  | V-false | ⊢ᵥfalse
  | error castError | ⊢ᵣcast-error | _ = WTenv-error

𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get eq) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  rewrite eq′
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe-corollary ⊢μ eq′
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | result ⟨ μ′ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ≡μ′ _ rewrite (sym μ≡μ′) = WTenv-result ⊢ρ
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  rewrite eq′
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe-corollary ⊢μ eq′
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | result ⟨ μ′ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ≡μ′ _ rewrite (sym μ≡μ′) = WTenv-result ⊢ρ
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error

𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁)
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-pres-⊢ₑ {Γ} {Δ} {γ} {ρ} {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ = WTenv-result (ext-update-pres-⊢ₑ hit μ″⊢ρ ⊢v″)
  where
  μ≡μ″ = trans μ≡μ′ μ′≡μ″
  μ″⊢ρ = subst (λ □ → Δ ∣ □ ⊢ₑ ρ) μ≡μ″ ⊢ρ
  hit = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ″ eq
... | no  _ = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ  {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-pres-⊢ₑ {Γ} {Δ} {γ} {ρ} {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ = WTenv-result (ext-update-pres-⊢ₑ hit μ″⊢ρ ⊢v″)
  where
  μ≡μ″ = trans μ≡μ′ μ′≡μ″
  μ″⊢ρ = subst (λ □ → Δ ∣ □ ⊢ₑ ρ) μ≡μ″ ⊢ρ
  hit = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ″ eq
... | no  _ = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = WTenv-timeout
𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = WTenv-error
𝒱-pres-⊢ₑ  {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ ⊢ρ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = WTenv-error

𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢new {T = T} {𝓁 = 𝓁} eq _) ⊢μ ⊢γ ⊢ρ fresh
 with pc ≼? 𝓁
... | no  _ = WTenv-error
... | yes _
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | v | ⊢v = WTenv-result (ext-new-pres-⊢ₑ fresh ⊢ρ ⊢v)

𝒱-pres-⊢ₑ {μ = μ} {pc} {suc k} (⊢new-dyn eq₁ eq₂) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁 | ⊢ᵥlabel | v | ⊢v
  with pc ≼? 𝓁
... | yes _ = WTenv-result (ext-new-pres-⊢ₑ fresh ⊢ρ ⊢v)
... | no  _ = WTenv-error

𝒱-pres-⊢ₑ {k = suc k} (⊢eq-ref eq₁ eq₂ _ _) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-ref loc | _ | V-ref loc′ | _ with loc ≟ₗ loc′
...   | yes _ = WTenv-result ⊢ρ
...   | no  _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢ƛ ⊢N) ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {γ = γ} {μ = μ} {pc} {suc k} (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} {𝓁̂₂} eq₁ eq₂ _ 𝓁̂₁′≾𝓁̂₁) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | v | ⊢v | w | ⊢w
  with castT μ pc T′ T w | ⊢castT {pc = pc} {T′} {T} ⊢μ ⊢w | castT-state-idem {pc = pc} {T′} {T} ⊢w
...   | timeout | ⊢ᵣtimeout | _ = WTenv-timeout
...   | error NSUError | ⊢ᵣnsu-error | _ = WTenv-error
...   | error castError | ⊢ᵣcast-error | _ = WTenv-error
...   | result ⟨ μ′ , w′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢w′ | ▹result μ≡μ′ _
  with castL μ′ pc′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {pc = pc′} 𝓁̂₁′≾𝓁̂₁ ⊢μ′
...     | timeout | ⊢ᵣtimeout = WTenv-timeout
...     | error NSUError | ⊢ᵣnsu-error = WTenv-error
...     | error castError | ⊢ᵣcast-error = WTenv-error
...     | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt rewrite μ≡μ′ = apply-pres-⊢ₑ {γ = γ} ⊢μ fresh ⊢v ⊢w′ ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢ref-label eq) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-ref loc | _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢lab-label eq) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} ⊢pc-label ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} ⊢label ⊢μ ⊢γ ⊢ρ fresh = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢≼ eq₁ eq₂) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ with 𝓁x ≼? 𝓁y
...   | yes _ = WTenv-result ⊢ρ
...   | no  _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢⊔ eq₁ eq₂) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢⊓ eq₁ eq₂) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {k = suc k} (⊢unlabel eq) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | ⊢ᵥlab _ ⊢v = WTenv-result ⊢ρ
... | V-lab 𝓁 v | ⊢ᵥlab-dyn ⊢v = WTenv-result ⊢ρ

𝒱-pres-⊢ₑ {γ = γ} {μ = μ} {pc} {suc k} (⊢to-label {M = M} {𝓁 = 𝓁} ⊢M _) ⊢μ ⊢γ ⊢ρ fresh
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-⊢ₑ {pc = pc} {k} ⊢M ⊢μ ⊢γ ⊢ρ fresh
... | timeout | ⊢ᵣtimeout | _ = WTenv-timeout
... | error NSUError | ⊢ᵣnsu-error | _ = WTenv-error
... | error castError | ⊢ᵣcast-error | _ = WTenv-error
... | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v | WTenv-result ⊢ρ′
  with pc′ ≼? (pc ⊔ 𝓁)
...   | yes _ = WTenv-result ⊢ρ′
...   | no  _ = WTenv-error

𝒱-pres-⊢ₑ {γ = γ} {μ = μ} {pc} {suc k} (⊢to-label-dyn {M = M} eq ⊢M) ⊢μ ⊢γ ⊢ρ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-label 𝓁 | _
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-⊢ₑ {pc = pc} {k} ⊢M ⊢μ ⊢γ ⊢ρ fresh
...   | timeout | ⊢ᵣtimeout | _ = WTenv-timeout
...   | error NSUError | ⊢ᵣnsu-error | _ = WTenv-error
...   | error castError | ⊢ᵣcast-error | _ = WTenv-error
...   | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v | WTenv-result ⊢ρ′
  with pc′ ≼? (pc ⊔ 𝓁)
...     | yes _ = WTenv-result ⊢ρ′
...     | no  _ = WTenv-error


𝒱-pres-WFaddr {k = 0} = λ _ _ _ _ → WFtimeout
𝒱-pres-WFaddr {M = ` x} {k = suc k} (⊢` eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq) =
  WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢tt ⊢μ ⊢γ fresh = WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢true ⊢μ ⊢γ fresh = WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢false ⊢μ ⊢γ fresh = WFresult fresh

𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢let {T = T} {T′} {M = M} {N} ⊢M ⊢N x) ⊢μ ⊢γ fresh
  with 𝒱 {Γ} γ M ⊢M μ pc k | 𝒱-pres-WFaddr {Γ} {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ fresh
    | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-⊢ₑ {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ ⊢γ fresh
... | timeout | WFtimeout | ⊢ᵣtimeout | WTenv-timeout = WFtimeout
... | error NSUError | WFerror | ⊢ᵣnsu-error | WTenv-error = WFerror
... | error castError | WFerror | ⊢ᵣcast-error | WTenv-error = WFerror
... | result ⟨ μ′ , v′ , pc′ ⟩ | WFresult fresh′ | ⊢ᵣresult ⊢μ′ ⊢v′ | WTenv-result μ′⊢γ
  with castT μ′ pc′ T′ T v′ | castT-state-idem {μ′} {pc′} {T′} {T} ⊢v′ | ⊢castT {μ′} {pc′} {T′} {T} ⊢μ′ ⊢v′
...   | result ⟨ μ″ , v″ , pc″ ⟩ | ▹result μ′≡μ″ _ | ⊢ᵣresult ⊢μ″ ⊢v″ =
  𝒱-pres-WFaddr {T ∷ Γ} {v″ ∷ γ} {pc = pc″} {k} ⊢N ⊢μ″ (⊢ₑ∷ ⊢v″ μ″⊢γ) fresh″
  where
  μ″⊢γ = subst (λ □ → Γ ∣ □ ⊢ₑ γ) μ′≡μ″ μ′⊢γ
  fresh″ = subst (λ □ → length □ ∉domₙ □) μ′≡μ″ fresh′
...   | timeout | ▹timeout | ⊢ᵣtimeout = WFtimeout
...   | error NSUError | ▹error | ⊢ᵣnsu-error = WFerror
...   | error castError | ▹error | ⊢ᵣcast-error = WFerror

𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢if {M = M} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh | V-true | ⊢ᵥtrue
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ fresh
𝒱-pres-WFaddr {k = suc k} (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  with castL μ′ pc′ 𝓁̂₂ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂⋎𝓁̂′ | ⊢castL {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂⋎𝓁̂′ ⊢μ′
    | castL-state-idem {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂⋎𝓁̂′
𝒱-pres-WFaddr {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  with castT μ″ pc″ T T″ vₘ | ⊢castT {μ″} {pc″} {T} {T″} ⊢μ″ ⊢vₘ″ | castT-state-idem {μ″} {pc″} {T} {T″} ⊢vₘ″
  where
  ⊢vₘ″ = subst (λ □ → □ ⊢ᵥ vₘ ⦂ T) μ′≡μ″ ⊢vₘ′
𝒱-pres-WFaddr {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | result ⟨ μ‴ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ″≡μ‴ _ = WFresult fresh″
  where
  fresh″ : length μ‴ ∉domₙ μ‴
  fresh″ = subst (λ □ → length □ ∉domₙ □) (trans μ′≡μ″ μ″≡μ‴) fresh′
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ′ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | timeout | ⊢ᵣtimeout | WFtimeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | error NSUError | ⊢ᵣnsu-error | WFerror = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-true | ⊢ᵥtrue
  | error castError | ⊢ᵣcast-error | WFerror = WFerror
𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢if {N = N} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh | V-false | ⊢ᵥfalse
  with 𝒱 γ N ⊢N μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢N | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {k} ⊢N ⊢μ ⊢γ fresh
𝒱-pres-WFaddr {k = suc k} (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  with castL μ′ pc′ 𝓁̂₂′ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂′⋎𝓁̂ | ⊢castL {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂′⋎𝓁̂ ⊢μ′
    | castL-state-idem {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} 𝓁̂≾𝓁̂′⋎𝓁̂
𝒱-pres-WFaddr {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  with castT μ″ pc″ T′ T″ vₙ | ⊢castT {μ″} {pc″} {T′} {T″} ⊢μ″ ⊢vₙ′ | castT-state-idem {μ″} {pc″} {T′} {T″} ⊢vₙ′
  where
  ⊢vₙ′ = subst (λ □ → □ ⊢ᵥ vₙ ⦂ T′) μ′≡μ″ ⊢vₙ
𝒱-pres-WFaddr {k = suc k} (⊢if {T = T} {T′} {T″} eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | result ⟨ μ‴ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ″≡μ‴ _ = WFresult fresh″
  where
  fresh″ : length μ‴ ∉domₙ μ‴
  fresh″ = subst (λ □ → length □ ∉domₙ □) (trans μ′≡μ″ μ″≡μ‴) fresh′
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | WFresult fresh′
  | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt | ▹result μ′≡μ″ _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult _ _ | WFresult _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | timeout | ⊢ᵣtimeout | WFtimeout = WFtimeout
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | error NSUError | ⊢ᵣnsu-error | WFerror = WFerror
𝒱-pres-WFaddr {k = suc k} (⊢if eq ⊢M ⊢N _) ⊢μ ⊢γ fresh
  | V-false | ⊢ᵥfalse
  | error castError | ⊢ᵣcast-error | WFerror = WFerror

𝒱-pres-WFaddr {k = suc k} (⊢get eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  rewrite eq′
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe-corollary ⊢μ eq′
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | result ⟨ μ′ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ≡μ′ _ = WFresult (subst (λ □ → length □ ∉domₙ □) μ≡μ′ fresh)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T′} {v = v} eq′
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  rewrite eq′
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe-corollary ⊢μ eq′
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | result ⟨ μ′ , _ , _ ⟩ | ⊢ᵣresult _ _ | ▹result μ≡μ′ _ = WFresult (subst (λ □ → length □ ∉domₙ □) μ≡μ′ fresh)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢get {T = T} eq) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T′} {v = v} eq′
  | error castError | ⊢ᵣcast-error | ▹error = WFerror

𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ = WFresult (ext-update-fresh fresh′ hit)
  where
  μ≡μ″ = trans μ≡μ′ μ′≡μ″
  fresh′ = subst (λ □ → length □ ∉domₙ □) μ≡μ″ fresh
  hit = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ″ eq
... | no  _ = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ = WFresult (ext-update-fresh fresh′ hit)
  where
  μ≡μ″ = trans μ≡μ′ μ′≡μ″
  fresh′ = subst (λ □ → length □ ∉domₙ □) μ≡μ″ fresh
  hit = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ″ eq
... | no  _ = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = WFtimeout
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = WFerror
𝒱-pres-WFaddr {μ = μ} {pc} {suc k} (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) ⊢μ ⊢γ fresh
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = WFerror

𝒱-pres-WFaddr {μ = μ} {pc} {k = suc k} (⊢new {T = T} {𝓁 = 𝓁} eq _) ⊢μ ⊢γ fresh
 with pc ≼? 𝓁
... | no  _ = WFerror
... | yes _
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | v | ⊢v = WFresult (ext-new-fresh {n = length μ} fresh refl)

𝒱-pres-WFaddr {μ = μ} {pc} {k = suc k} (⊢new-dyn eq₁ eq₂) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁 | ⊢ᵥlabel | v | ⊢v
  with pc ≼? 𝓁
... | yes _ = WFresult (ext-new-fresh {n = length μ} fresh refl)
... | no  _ = WFerror

𝒱-pres-WFaddr {k = suc k} (⊢eq-ref eq₁ eq₂ _ _) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-ref loc | _ | V-ref loc′ | _ with loc ≟ₗ loc′
...   | yes _ = WFresult fresh
...   | no  _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢ƛ ⊢N) ⊢μ ⊢γ fresh = WFresult fresh

𝒱-pres-WFaddr {γ = γ} {μ = μ} {pc} {k = suc k} (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} {𝓁̂₂} eq₁ eq₂ _ 𝓁̂₁′≾𝓁̂₁) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | v | ⊢v | w | ⊢w
  with castT μ pc T′ T w | ⊢castT {pc = pc} {T′} {T} ⊢μ ⊢w | castT-state-idem {pc = pc} {T′} {T} ⊢w
...   | timeout | ⊢ᵣtimeout | _ = WFtimeout
...   | error NSUError | ⊢ᵣnsu-error | _ = WFerror
...   | error castError | ⊢ᵣcast-error | _ = WFerror
...   | result ⟨ μ′ , w′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢w′ | ▹result μ≡μ′ _
  with castL μ′ pc′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {pc = pc′} 𝓁̂₁′≾𝓁̂₁ ⊢μ′
...     | timeout | ⊢ᵣtimeout = WFtimeout
...     | error NSUError | ⊢ᵣnsu-error = WFerror
...     | error castError | ⊢ᵣcast-error = WFerror
...     | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt rewrite μ≡μ′ = apply-pres-WFaddr {γ = γ} ⊢μ fresh ⊢v ⊢w′

𝒱-pres-WFaddr {k = suc k} (⊢ref-label eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-ref loc | _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢lab-label eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} ⊢pc-label ⊢μ ⊢γ fresh = WFresult fresh

𝒱-pres-WFaddr {k = suc k} ⊢label ⊢μ ⊢γ fresh = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢≼ eq₁ eq₂) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ with 𝓁x ≼? 𝓁y
...   | yes _ = WFresult fresh
...   | no  _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢⊔ eq₁ eq₂) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢⊓ eq₁ eq₂) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = WFresult fresh

𝒱-pres-WFaddr {k = suc k} (⊢unlabel eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | ⊢ᵥlab _ ⊢v = WFresult fresh
... | V-lab 𝓁 v | ⊢ᵥlab-dyn ⊢v = WFresult fresh

𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢to-label {M = M} {𝓁 = 𝓁} ⊢M _) ⊢μ ⊢γ fresh
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-WFaddr {pc = pc} {k} ⊢M ⊢μ ⊢γ fresh
... | timeout | ⊢ᵣtimeout | _ = WFtimeout
... | error NSUError | ⊢ᵣnsu-error | _ = WFerror
... | error castError | ⊢ᵣcast-error | _ = WFerror
... | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v | WFresult fresh′
  with pc′ ≼? (pc ⊔ 𝓁)
...   | yes _ = WFresult fresh′
...   | no  _ = WFerror

𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢to-label-dyn {M = M} eq ⊢M) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-label 𝓁 | _
  with 𝒱 γ M ⊢M μ pc k | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-WFaddr {pc = pc} {k} ⊢M ⊢μ ⊢γ fresh
...   | timeout | ⊢ᵣtimeout | _ = WFtimeout
...   | error NSUError | ⊢ᵣnsu-error | _ = WFerror
...   | error castError | ⊢ᵣcast-error | _ = WFerror
...   | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v | WFresult fresh′
  with pc′ ≼? (pc ⊔ 𝓁)
...     | yes _ = WFresult fresh′
...     | no  _ = WFerror


apply-safe {μ = μ} {pc} {k} ⊢μ fresh (⊢ᵥclos {Δ} {γ = ρ} ⊢ρ ⊢N) ⊢w = 𝒱-safe k pc ⊢μ fresh (⊢ₑ∷ ⊢w ⊢ρ) ⊢N
apply-safe {γ} {w = w} {μ} {pc} {k} ⊢μ fresh (⊢ᵥproxy {S = S} {T} {S′} {T′} {v} {𝓁̂₁} {𝓁̂₂} {𝓁̂₁′} {𝓁̂₂′} {𝓁̂₁′≾𝓁̂₁ = 𝓁̂₁′≾𝓁̂₁} {𝓁̂₂≾𝓁̂₂′} ⊢v) ⊢w
  with castT μ pc S′ S w | ⊢castT {pc = pc} {S′} {S} ⊢μ ⊢w | castT-state-idem {μ} {pc} {S′} {S} ⊢w
... | timeout | _ | _ = ⊢ᵣtimeout
... | error NSUError | _ | _ = ⊢ᵣnsu-error
... | error castError | _ | _ = ⊢ᵣcast-error
... | result ⟨ μ₁ , w′ , pc₁ ⟩ | ⊢ᵣresult ⊢μ₁ ⊢w′ | ▹result μ≡μ₁ _
  with castL μ₁ pc₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁ ⊢μ₁ | castL-state-idem {μ₁} {pc₁} 𝓁̂₁′≾𝓁̂₁
...   | timeout | _ | _ = ⊢ᵣtimeout
...   | error NSUError | _ | _ = ⊢ᵣnsu-error
...   | error castError | _ | _ = ⊢ᵣcast-error
...   | result ⟨ μ₂ , _ , pc₂ ⟩ | ⊢ᵣresult ⊢μ₂ _ | ▹result μ₁≡μ₂ _
  with apply γ v w′ μ₂ pc₂ k | apply-safe {γ} {pc = pc₂} {k} ⊢μ₂ freshμ₂ μ₂⊢v μ₂⊢w′
  where
  freshμ₂ = subst (λ □ → length □ ∉domₙ □) (trans μ≡μ₁ μ₁≡μ₂) fresh
  μ₂⊢v = subst (λ □ → □ ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T) (trans μ≡μ₁ μ₁≡μ₂) ⊢v
  μ₂⊢w′ = subst (λ □ → □ ⊢ᵥ w′ ⦂ S) μ₁≡μ₂ ⊢w′
...     | timeout | _ = ⊢ᵣtimeout
...     | error NSUError | _ = ⊢ᵣnsu-error
...     | error castError | _ = ⊢ᵣcast-error
...     | result ⟨ μ₃ , v₁ , pc₃ ⟩ | ⊢ᵣresult ⊢μ₃ ⊢v₁
  with castL μ₃ pc₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′ | ⊢castL {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′ ⊢μ₃ | castL-state-idem {μ₃} {pc₃} 𝓁̂₂≾𝓁̂₂′
...       | timeout | _ | _ = ⊢ᵣtimeout
...       | error NSUError | _ | _ = ⊢ᵣnsu-error
...       | error castError | _ | _ = ⊢ᵣcast-error
...       | result ⟨ μ₄ , _ , pc₄ ⟩ | ⊢ᵣresult ⊢μ₄ _ | ▹result μ₃≡μ₄ _ rewrite (sym μ₃≡μ₄) = ⊢castT {pc = pc₄} {T} {T′} ⊢μ₄ ⊢v₁

𝒱-safe 0 _ _ _ _ _ = ⊢ᵣtimeout

𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢tt = ⊢ᵣresult ⊢μ ⊢ᵥtt
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢true = ⊢ᵣresult ⊢μ ⊢ᵥtrue
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢false = ⊢ᵣresult ⊢μ ⊢ᵥfalse
𝒱-safe (suc k) pc₀ ⊢μ _ ⊢γ ⊢label = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe {γ = γ} {M = (` x)} (suc k) pc₀ ⊢μ _ ⊢γ (⊢` eq) rewrite proj₂ (⊢γ→∃v ⊢γ eq) =
  ⊢ᵣresult ⊢μ (⊢γ→⊢v ⊢γ eq)

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
--   : Goes to the M branch
𝒱-safe {γ = γ} {M = if `x M N} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  -- Case split on the evaluation of M
  with 𝒱 γ M ⊢M μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢M
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  with (l̂ pc′) ≾? (𝓁̂₂ ⋎ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  | yes _
  with 𝓁̂₂ ≾? (𝓁̂₂ ⋎ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T∨T′≡T″)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  | yes _
  | yes _
  with T ≲? T″
... | yes T≲T″ = ⊢castT′ T≲T″ ⊢μ′ ⊢vₘ
... | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  | yes _
  | no oops = ⊥-elim (oops 𝓁̂≾𝓁̂⋎𝓁̂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
--   : Goes to the N branch
𝒱-safe {γ = γ} {M = if `x M N} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  with 𝒱 γ N ⊢N μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢N  -- Case split on the evaluation of N
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  with (l̂ pc′) ≾? (𝓁̂₂ ⋎ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  | yes _
  with 𝓁̂₂′ ≾? (𝓁̂₂ ⋎ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T∨T′≡T″)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  | yes _
  | yes _
  with T′ ≲? T″
... | yes T′≲T″ = ⊢castT′ T′≲T″ ⊢μ′ ⊢vₙ
... | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  | yes _
  | no oops = ⊥-elim (oops 𝓁̂≾𝓁̂′⋎𝓁̂)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢get {T = T} eq)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢get {T = T} eq)
  | V-ref loc | ⊢ᵥref {T = T′} eq′
  rewrite eq′
  with T′ ≲? T
... | yes T′≲T = ⊢castT′ T′≲T ⊢μ (lookup-safe-corollary ⊢μ eq′)
... | no  _ = ⊢ᵣcast-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢get {T = T} eq)
  | V-ref loc | ⊢ᵥref-dyn {T = T′} eq′
  rewrite eq′
  with T′ ≲? T
... | yes T′≲T = ⊢castT′ T′≲T ⊢μ (lookup-safe-corollary ⊢μ eq′)
... | no _ = ⊢ᵣcast-error

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc₀ ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc₀ ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc₀ ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ =
  let eq′ = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ′ eq in
  let eq″ = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ′≡μ″ eq′ in
  ⊢ᵣresult (ext-update-pres-⊢ₛ (⊢ₛ∷ ⊢v″ ⊢μ″) eq″ ⊢v″) ⊢ᵥtt
... | no  _ = ⊢ᵣnsu-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref loc | ⊢ᵥref-dyn eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  rewrite eq
  with castT μ (pc₀ ⊔ 𝓁₂) T′ T v | ⊢castT {μ} {pc₀ ⊔ 𝓁₂} {T′} {T} ⊢μ ⊢v | castT-state-idem {μ} {pc₀ ⊔ 𝓁₂} {T′} {T} {v} ⊢v
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  with castT μ′ pc′ T T″ v′ | ⊢castT {μ′} {pc′} {T} {T″} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T} {T″} {v′} ⊢v′
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} {v = w} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result μ≡μ′ _
  | result ⟨ u″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ _
  with pc″ ≼? 𝓁₂
... | yes _ =
  let eq′ = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ≡μ′ eq in
  let eq″ = subst (λ □ → lookup □ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≡ just ⟨ T″ , w ⟩) μ′≡μ″ eq′ in
  ⊢ᵣresult (ext-update-pres-⊢ₛ (⊢ₛ∷ ⊢v″ ⊢μ″) eq″ ⊢v″) ⊢ᵥtt
... | no  _ = ⊢ᵣnsu-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn {T = T″} eq
  | v | ⊢v
  | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | ▹result _ _
  | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error
𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set {T = T} {T′} eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂)
  | V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | ⊢ᵥref-dyn eq
  | v | ⊢v
  | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error

𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢new {T = T} {𝓁 = 𝓁} eq 𝓁̂₁≲𝓁) with pc₀ ≼? 𝓁
... | no  _ = ⊢ᵣnsu-error
... | yes _
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | v | ⊢v =
  ⊢ᵣresult ⊢v∷μ (⊢ᵥref (ext-lookup-first {μ} {⟨ length μ , pc₀ , 𝓁 ⟩}))
  where
  ⊢v∷μ : ⟨ length μ , pc₀ , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ ⊢ₛ ⟨ length μ , pc₀ , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ
  ⊢v∷μ = ext-new-pres-⊢ₛ (⊢ₛ∷ ⊢v ⊢μ) fresh ⊢v

𝒱-safe {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢new-dyn {T = T} eq₁ eq₂)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁 | ⊢ᵥlabel | v | ⊢v
  with pc₀ ≼? 𝓁
...   | yes _ = ⊢ᵣresult ⊢v∷μ (⊢ᵥref-dyn (ext-lookup-first {μ} {⟨ length μ , pc₀ , 𝓁 ⟩}))
  where
  ⊢v∷μ : ⟨ length μ , pc₀ , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ ⊢ₛ ⟨ length μ , pc₀ , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ
  ⊢v∷μ = ext-new-pres-⊢ₛ (⊢ₛ∷ ⊢v ⊢μ) fresh ⊢v
...   | no  _ = ⊢ᵣnsu-error

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢eq-ref eq₁ eq₂ _ _)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-ref loc | _ | V-ref loc′ | _ with loc ≟ₗ loc′
...   | yes _ = ⊢ᵣresult ⊢μ ⊢ᵥtrue
...   | no  _ = ⊢ᵣresult ⊢μ ⊢ᵥfalse

𝒱-safe {Γ} {γ} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢let {T = T} {T′ = T′} {M = M} ⊢M ⊢N T′≲T)
  with 𝒱 {Γ} γ M ⊢M μ pc₀ k | 𝒱-safe {Γ} k pc₀ ⊢μ fresh ⊢γ ⊢M
    | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc₀} {k} ⊢M ⊢μ ⊢γ fresh | 𝒱-pres-⊢ₑ {pc = pc₀} {k} ⊢M ⊢μ ⊢γ ⊢γ fresh
... | timeout | ⊢ᵣtimeout | WFtimeout | _ = ⊢ᵣtimeout
... | error NSUError | ⊢ᵣnsu-error | _ | _ = ⊢ᵣnsu-error
... | error castError | ⊢ᵣcast-error | _ | _ = ⊢ᵣcast-error
... | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | WFresult fresh′ | WTenv-result μ′⊢γ
  with castT μ′ pc′ T′ T v′ | ⊢castT {μ′} {pc′} {T′} {T} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T′} {T} ⊢v′
...   | result ⟨ μ″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ pc′≡pc″ =
  𝒱-safe k pc″ ⊢μ″ fresh″ (⊢ₑ∷ ⊢v″ μ″⊢γ) ⊢N
  where
  fresh″ = subst (λ □ → length □ ∉domₙ □) μ′≡μ″ fresh′
  μ″⊢γ = subst (λ □ → Γ ∣ □ ⊢ₑ γ) μ′≡μ″ μ′⊢γ
...   | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error

𝒱-safe {Γ} {γ} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} {𝓁̂₂} eq₁ eq₂ _ 𝓁̂₁′≾𝓁̂₁)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | v | ⊢v | w | ⊢w
  with castT μ pc₀ T′ T w | ⊢castT {pc = pc₀} {T′} {T} ⊢μ ⊢w | castT-state-idem {μ} {pc₀} {T′} {T} ⊢w
...   | timeout | ⊢ᵣtimeout | _ = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error | _ = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error | _ = ⊢ᵣcast-error
...   | result ⟨ μ′ , w′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢w′ | ▹result μ≡μ′ _
  with castL μ′ pc′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | ⊢castL {pc = pc′} 𝓁̂₁′≾𝓁̂₁ ⊢μ′
...     | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
...     | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
...     | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
...     | result ⟨ μ″ , _ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢ᵥtt = apply-safe {γ = γ} {pc = pc₀} {k} ⊢μ fresh ⊢v μ⊢w′
  where
  μ⊢w′ = subst (λ □ → □ ⊢ᵥ w′ ⦂ T) (sym μ≡μ′) ⊢w′

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢ƛ ⊢N) = ⊢ᵣresult ⊢μ (⊢ᵥclos ⊢γ ⊢N)

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢ref-label eq)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-ref loc | _ = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢lab-label eq)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | _ = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ ⊢pc-label = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢⊔ eq₁ eq₂)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢⊓ eq₁ eq₂)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ = ⊢ᵣresult ⊢μ ⊢ᵥlabel

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢≼ eq₁ eq₂)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | V-label 𝓁x | _ | V-label 𝓁y | _ with 𝓁x ≼? 𝓁y
...   | yes _ = ⊢ᵣresult ⊢μ ⊢ᵥtrue
...   | no  _ = ⊢ᵣresult ⊢μ ⊢ᵥfalse

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢unlabel eq)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-lab 𝓁 v | ⊢ᵥlab _ ⊢v = ⊢ᵣresult ⊢μ ⊢v
... | V-lab 𝓁 v | ⊢ᵥlab-dyn ⊢v = ⊢ᵣresult ⊢μ ⊢v

𝒱-safe {γ = γ} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢to-label {M = M} {𝓁 = 𝓁} ⊢M _)
  with 𝒱 γ M ⊢M μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢M
... | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
... | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
... | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
... | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v with pc′ ≼? (pc₀ ⊔ 𝓁)
...   | yes _ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab ≼-refl ⊢v)
...   | no  _ = ⊢ᵣnsu-error

𝒱-safe {γ = γ} {μ = μ} (suc k) pc₀ ⊢μ fresh ⊢γ (⊢to-label-dyn {M = M} eq ⊢M)
  rewrite proj₂ (⊢γ→∃v ⊢γ eq)
  with proj₁ (⊢γ→∃v ⊢γ eq) | (⊢γ→⊢v ⊢γ eq)
... | V-label 𝓁 | _ with 𝒱 γ M ⊢M μ pc₀ k | 𝒱-safe k pc₀ ⊢μ fresh ⊢γ ⊢M
...   | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
...   | result ⟨ μ′ , v , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v with pc′ ≼? (pc₀ ⊔ 𝓁)
...     | yes _ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab-dyn ⊢v)
...     | no  _ = ⊢ᵣnsu-error
