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

𝒱-pres-⊢ₑ : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ pc k}
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → WTenv (𝒱 γ M ⊢M μ pc k) Γ γ

𝒱-safe : ∀ {Γ γ T M 𝓁̂₁ 𝓁̂₂ μ}
  → (k : ℕ)
  → (pc₀ : ℒ)
  → μ ⊢ₛ μ
  → length μ ∉domₙ μ
  → Γ ∣ μ ⊢ₑ γ
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 γ M ⊢M μ pc₀ k ⦂ T

𝒱-pres-WFaddr {k = 0} = λ _ _ _ _ → WFtimeout
𝒱-pres-WFaddr {M = ` x} {k = suc k} (⊢` eq) ⊢μ ⊢γ fresh
  rewrite proj₂ (⊢γ→∃v ⊢γ eq) =
  WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢tt ⊢μ ⊢γ fresh = WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢true ⊢μ ⊢γ fresh = WFresult fresh
𝒱-pres-WFaddr {k = suc k} ⊢false ⊢μ ⊢γ fresh = WFresult fresh

𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc} {suc k} (⊢let {T = T} {T′} {M = M} {N} ⊢M ⊢N x) ⊢μ ⊢γ fresh
  with 𝒱 {Γ} γ M ⊢M μ pc k | 𝒱-pres-WFaddr {Γ} {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ fresh
    | 𝒱-safe k pc ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-⊢ₑ {Γ} {γ} {μ = μ} {pc} {k} ⊢M ⊢μ ⊢γ
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
  with castL μ′ pc′ 𝓁̂₂ (𝓁̂₂ ⊔̂ 𝓁̂₂′) 𝓁̂≾𝓁̂⊔̂𝓁̂′ | ⊢castL {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⊔̂ 𝓁̂₂′} 𝓁̂≾𝓁̂⊔̂𝓁̂′ ⊢μ′
    | castL-state-idem {μ′} {pc′} {𝓁̂₂} {𝓁̂₂ ⊔̂ 𝓁̂₂′} 𝓁̂≾𝓁̂⊔̂𝓁̂′
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
  with castL μ′ pc′ 𝓁̂₂′ (𝓁̂₂ ⊔̂ 𝓁̂₂′) 𝓁̂≾𝓁̂′⊔̂𝓁̂ | ⊢castL {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⊔̂ 𝓁̂₂′} 𝓁̂≾𝓁̂′⊔̂𝓁̂ ⊢μ′
    | castL-state-idem {μ′} {pc′} {𝓁̂₂′} {𝓁̂₂ ⊔̂ 𝓁̂₂′} 𝓁̂≾𝓁̂′⊔̂𝓁̂
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
-- 𝒱-pres-WFaddr (⊢get x) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢set x x₁ x₂ x₃) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢new x x₁) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢new-dyn x x₁) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢eq-ref x x₁ x₂ x₃) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢ƛ tM) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢· x x₁ x₂ x₃) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢ref-label x) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢lab-label x) fresh = {!!}
-- 𝒱-pres-WFaddr ⊢pc-label fresh = {!!}
-- 𝒱-pres-WFaddr ⊢label fresh = {!!}
-- 𝒱-pres-WFaddr (⊢≼ x x₁) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢⊔ x x₁) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢⊓ x x₁) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢unlabel x) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢to-label tM x) fresh = {!!}
-- 𝒱-pres-WFaddr (⊢to-label-dyn x tM) fresh = {!!}



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
  with (l̂ pc′) ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-true | ⊢ᵥ-true
  | result ⟨ μ′ , vₘ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ
  | yes _
  with 𝓁̂₂ ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T⋎T′≡T″)
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
  | no oops = ⊥-elim (oops 𝓁̂≾𝓁̂⊔̂𝓁̂′)
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
  with (l̂ pc′) ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N _)
  | V-false | ⊢ᵥ-false
  | result ⟨ μ′ , vₙ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ
  | yes _
  with 𝓁̂₂′ ≾? (𝓁̂₂ ⊔̂ 𝓁̂₂′)
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢if {T = T} {T′} {T″} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq ⊢M ⊢N T⋎T′≡T″)
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
  | no oops = ⊥-elim (oops 𝓁̂≾𝓁̂′⊔̂𝓁̂)
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
  with 𝒱 {Γ} γ M ⊢M μ pc₀ k | 𝒱-safe {Γ} k pc₀ ⊢μ fresh ⊢γ ⊢M | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ} {pc₀} {k} ⊢M ⊢μ ⊢γ fresh
... | timeout | ⊢ᵣtimeout | WFtimeout = ⊢ᵣtimeout
... | error NSUError | ⊢ᵣnsu-error | _ = ⊢ᵣnsu-error
... | error castError | ⊢ᵣcast-error | _ = ⊢ᵣcast-error
... | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | WFresult fresh′
  with castT μ′ pc′ T′ T v′ | ⊢castT {μ′} {pc′} {T′} {T} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {pc′} {T′} {T} ⊢v′
...   | result ⟨ μ″ , v″ , pc″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ pc′≡pc″ =
  𝒱-safe k pc″ ⊢μ″ (subst (λ □ → length □ ∉domₙ □) μ′≡μ″ fresh′) (⊢ₑ∷ ⊢v″ {!!}) ⊢N
...   | timeout | ⊢ᵣtimeout | ▹timeout = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error | ▹error = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error | ▹error = ⊢ᵣcast-error

𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢· _ _ _ _) = {!!}

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


-- Start with empty env and store.
type-safety : ∀ {T M 𝓁̂₁ 𝓁̂₂}
  → (k : ℕ)
  → (pc₀ : ℒ)
  → (⊢M : [] [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
    ----------------------------
  → ⊢ᵣ 𝒱 [] M ⊢M [] pc₀ k ⦂ T
type-safety k pc₀ ⊢M = 𝒱-safe k pc₀ ⊢ₛ∅ ∉domₙ∅ ⊢ₑ∅ ⊢M
