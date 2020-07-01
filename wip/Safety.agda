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




-- Matches program state ⟨ μ , pc ⟩ from a configuration.
infix 10 _▹_,_

data _▹_,_ : Result Conf → Store → ℒ → Set where

  ▹error : ∀ {μ pc err} → error err ▹ μ , pc

  ▹timeout : ∀ {μ pc} → timeout ▹ μ , pc

  ▹result : ∀ {μ μ′ v pc pc′}
    → μ′ ≡ μ
    → pc′ ≡ pc
    → result ⟨ μ , v , pc ⟩ ▹ μ′ , pc′

castT′-state-idem : ∀ {μ pc T₁ T₂ v}
  → (T₁≲T₂ : T₁ ≲ T₂)
  → μ ⊢ᵥ v ⦂ T₁
  → castT′ μ pc T₁ T₂ T₁≲T₂ v ▹ μ , pc
castT′-state-idem ≲-⊤ ⊢ᵥtt = ▹result refl refl
castT′-state-idem ≲-𝔹 ⊢ᵥtrue = ▹result refl refl
castT′-state-idem ≲-𝔹 ⊢ᵥfalse = ▹result refl refl
castT′-state-idem ≲-ℒ ⊢ᵥlabel = ▹result refl refl
castT′-state-idem (≲-⇒ _ _ _ _) (⊢ᵥclos ⊢γ ⊢M) = ▹result refl refl
castT′-state-idem (≲-⇒ _ _ _ _) (⊢ᵥproxy ⊢v) = ▹result refl refl
castT′-state-idem {v = V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩} (≲-Ref {𝓁̂₁} {𝓁̂₂} _ _ _ _) (⊢ᵥref eq)
  with 𝓁̂₂
... | ¿ = ▹result refl refl
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {v = V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩} (≲-Ref {𝓁̂₁} {𝓁̂₂} _ _ _ _) (⊢ᵥref-dyn eq)
  with 𝓁̂₂
... | ¿ = ▹result refl refl
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {μ} {pc} {v = V-lab 𝓁 v} (≲-Lab {𝓁̂₁} {𝓁̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab 𝓁≼𝓁′ ⊢v)
  with (l̂ 𝓁) ≾? 𝓁̂₂
... | no  _ = ▹error
... | yes _ with castT′ μ pc T₁ T₂ T₁≲T₂ v | castT′-state-idem {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ▹result μ≡μ′ pc≡pc′ = ▹result μ≡μ′ pc≡pc′
...   | timeout | ▹timeout = ▹timeout
...   | error _ | ▹error = ▹error
castT′-state-idem {μ} {pc} {v = V-lab 𝓁 v} (≲-Lab {𝓁̂₁} {𝓁̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab-dyn ⊢v)
  with (l̂ 𝓁) ≾? 𝓁̂₂
... | no  _ = ▹error
... | yes _ with castT′ μ pc T₁ T₂ T₁≲T₂ v | castT′-state-idem {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ▹result μ≡μ′ pc≡pc′ = ▹result μ≡μ′ pc≡pc′
...   | timeout | ▹timeout = ▹timeout
...   | error _ | ▹error = ▹error


castT-state-idem : ∀ {μ pc T₁ T₂ v}
  → μ ⊢ᵥ v ⦂ T₁
  → castT μ pc T₁ T₂ v ▹ μ , pc
castT-state-idem {μ} {pc} {T₁} {T₂} {v} ⊢v with T₁ ≲? T₂
... | yes T₁≲T₂ = castT′-state-idem T₁≲T₂ ⊢v
... | no  _     = ▹error

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
𝒱-safe (suc k) pc₀ ⊢μ fresh ⊢γ (⊢set eq₁ eq₂ T′≲T 𝓁̂₁≾𝓁̂) | V-ref loc | ⊢ᵥref-dyn eq = {!!}

-- Start with empty env and store.
-- type-safety : ∀ {T M 𝓁̂₁ 𝓁̂₂ pc₀}
--   → (k : ℕ)
--   → (⊢M : [] [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
--     ----------------------------
--   → ⊢ᵣ 𝒱 [] M ⊢M [] pc₀ k ⦂ T
-- type-safety k ⊢M = 𝒱-safe k ⊢ₛ∅ ∉domₙ∅ ⊢ₑ∅ ⊢M
