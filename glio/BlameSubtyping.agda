open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties using (m≤m⊔n)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_; length)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; trans; subst; inspect; [_])
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import StaticsGLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Lemmas
open import Interp
open import WellTypedness using (_⊢ᵥ_⦂_)
open _⊢ᵥ_⦂_
open import Store
open import WellTypedness
open import CastStateIdem
open import InterpSafe
open import Subtyping


private
  timeout≢result : ∀ {conf : Conf} → timeout ≢ result conf
  timeout≢result ()

  error≢result : ∀ {err} {conf : Conf} → error err ≢ result conf
  error≢result ()

  result≡→𝓁ᶜ≡ : ∀ {μ₁ μ₂ : Store} {v₁ v₂ : Value} {𝓁ᶜ₁ 𝓁ᶜ₂ : ℒ}
    → result ⟨ μ₁ , v₁ , 𝓁ᶜ₁ ⟩ ≡ result ⟨ μ₂ , v₂ , 𝓁ᶜ₂ ⟩
    → 𝓁ᶜ₁ ≡ 𝓁ᶜ₂
  result≡→𝓁ᶜ≡ res≡ =
    let conf₁≡conf₂ = result-≡-inv res≡ in
    let cdr₁≡cdr₂ = proj₂ (×-≡-inv conf₁≡conf₂) in
      proj₂ (×-≡-inv cdr₁≡cdr₂)

  castL→𝓁ᶜ≡ : ∀ {μ₁ μ₂ 𝓁ᶜ₁ 𝓁ᶜ₂ 𝓁̂₁ 𝓁̂₂ v}
    → (𝓁̂₁≾𝓁̂₂ : 𝓁̂₁ ≾ 𝓁̂₂)
    → castL μ₁ 𝓁ᶜ₁ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁≾𝓁̂₂ ≡ result ⟨ μ₂ , v , 𝓁ᶜ₂ ⟩
    → 𝓁ᶜ₁ ≡ 𝓁ᶜ₂
  castL→𝓁ᶜ≡ {𝓁ᶜ₁ = 𝓁ᶜ₁} {𝓁̂₁ = 𝓁̂₁} {𝓁̂₂} 𝓁₁≾𝓁₂ eq with (l̂ 𝓁ᶜ₁) ≾? 𝓁̂₂
  ... | yes _ = result≡→𝓁ᶜ≡ eq
  ... | no  _ = ⊥-elim (error≢result eq)

  castT′→𝓁ᶜ≡ : ∀ {μ₁ μ₂ 𝓁ᶜ₁ 𝓁ᶜ₂ v₂ T₁ T₂}
    → (T₁≲T₂ : T₁ ≲ T₂)
    → (v₁ : Value)
    → castT′ μ₁ 𝓁ᶜ₁ T₁ T₂ T₁≲T₂ v₁ ≡ result ⟨ μ₂ , v₂ , 𝓁ᶜ₂ ⟩
    → 𝓁ᶜ₁ ≡ 𝓁ᶜ₂
  castT′→𝓁ᶜ≡ ≲-⊤ V-tt eq = result≡→𝓁ᶜ≡ eq
  castT′→𝓁ᶜ≡ ≲-𝔹 V-true eq = result≡→𝓁ᶜ≡ eq
  castT′→𝓁ᶜ≡ ≲-𝔹 V-false eq = result≡→𝓁ᶜ≡ eq
  castT′→𝓁ᶜ≡ ≲-ℒ (V-label _) eq = result≡→𝓁ᶜ≡ eq
  castT′→𝓁ᶜ≡ (≲-Ref {𝓁̂₂ = 𝓁̂₂} _ _ _ _) (V-ref ⟨ _ , _ , 𝓁₂ ⟩) eq with 𝓁̂₂
  ... | ¿ = result≡→𝓁ᶜ≡ eq
  ... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
  ...   | yes _ = result≡→𝓁ᶜ≡ eq
  ...   | no  _ = ⊥-elim (error≢result eq)
  castT′→𝓁ᶜ≡ {μ₁} {μ₂} {𝓁ᶜ₁} (≲-Lab {𝓁̂₂ = 𝓁̂₂} _ T₁≲T₂) (V-lab 𝓁 v) eq with (l̂ 𝓁) ≾? 𝓁̂₂
  ... | no _ = ⊥-elim (error≢result eq)
  ... | yes _ with castT′ μ₁ 𝓁ᶜ₁ _ _ T₁≲T₂ v | inspect (λ v → castT′ μ₁ 𝓁ᶜ₁ _ _ T₁≲T₂ v) v
  ...   | result ⟨ μ′ , v′ , 𝓁ᶜ′ ⟩ | [ eq₁ ] =
    let 𝓁ᶜ₁≡𝓁ᶜ′ = castT′→𝓁ᶜ≡ T₁≲T₂ v eq₁ in
    let 𝓁ᶜ′≡𝓁ᶜ₂ = result≡→𝓁ᶜ≡ eq in
      trans 𝓁ᶜ₁≡𝓁ᶜ′ 𝓁ᶜ′≡𝓁ᶜ₂
  ...   | error err | _ = ⊥-elim (error≢result eq)
  ...   | timeout | _ = ⊥-elim (timeout≢result eq)
  castT′→𝓁ᶜ≡ (≲-⇒ _ _ _ _) (V-clos _) eq = result≡→𝓁ᶜ≡ eq
  castT′→𝓁ᶜ≡ (≲-⇒ _ _ _ _) (V-proxy _ _ _ _ _ _ _ _  _ _ _ _ _) eq = result≡→𝓁ᶜ≡ eq

  castT→𝓁ᶜ≡ : ∀ {μ₁ μ₂ 𝓁ᶜ₁ 𝓁ᶜ₂ v₂ T₁ T₂}
    → (v₁ : Value)
    → castT μ₁ 𝓁ᶜ₁ T₁ T₂ v₁ ≡ result ⟨ μ₂ , v₂ , 𝓁ᶜ₂ ⟩
    → 𝓁ᶜ₁ ≡ 𝓁ᶜ₂
  castT→𝓁ᶜ≡ {T₁ = T₁} {T₂} v₁ eq with T₁ ≲? T₂
  ... | yes T₁≲T₂ = castT′→𝓁ᶜ≡ T₁≲T₂ v₁ eq
  ... | no _ = ⊥-elim (error≢result eq)

  castL-no-blame-inv : ∀ {μ μ′ 𝓁̂₁ 𝓁̂₂ 𝓁ᶜ 𝓁ᶜ′ v}
    → (𝓁̂₁≾𝓁̂₂ : 𝓁̂₁ ≾ 𝓁̂₂)
    → castL μ 𝓁ᶜ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁≾𝓁̂₂ ≡ result ⟨ μ′ , v , 𝓁ᶜ′ ⟩
    → (l̂ 𝓁ᶜ) ≾ 𝓁̂₂
  castL-no-blame-inv {𝓁̂₂ = 𝓁̂₂} {𝓁ᶜ = 𝓁ᶜ} _ eq with (l̂ 𝓁ᶜ) ≾? 𝓁̂₂
  ... | yes 𝓁ᶜ≾𝓁₂ = 𝓁ᶜ≾𝓁₂

apply-pc≾ : ∀ {Γ γ μ μ′ T S 𝓁̂₁ 𝓁̂₂ 𝓁ᶜ 𝓁ᶜ′ v w v′ k}
  → (l̂ 𝓁ᶜ) ≾ 𝓁̂₁
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → length μ ∉domₙ μ
  → μ ⊢ᵥ v ⦂ T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S
  → μ ⊢ᵥ w ⦂ T
  → apply γ v w μ 𝓁ᶜ k ≡ result ⟨ μ′ , v′ , 𝓁ᶜ′ ⟩
  → (l̂ 𝓁ᶜ′) ≾ 𝓁̂₂

𝒱-pres-pc≲ : ∀ {Γ γ μ₁ μ₂ 𝓁ᶜ₁ 𝓁ᶜ₂ 𝓁̂₁ 𝓁̂₂ M v T}
  → (k : ℕ)
  → (l̂ 𝓁ᶜ₁) ≾ 𝓁̂₁
  → μ₁ ⊢ₛ μ₁
  → Γ ∣ μ₁ ⊢ₑ γ
  → length μ₁ ∉domₙ μ₁
  → (⊢M : Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T)
  → 𝒱 γ M ⊢M μ₁ 𝓁ᶜ₁ k ≡ result ⟨ μ₂ , v , 𝓁ᶜ₂ ⟩
    -------------------------------------------
  → (l̂ 𝓁ᶜ₂) ≾ 𝓁̂₂

apply-pc≾ {k = k} 𝓁ᶜ≾𝓁₁ ⊢μ _ fresh (⊢ᵥclos ⊢γ ⊢M) ⊢w eq = 𝒱-pres-pc≲ k 𝓁ᶜ≾𝓁₁ ⊢μ (⊢ₑ∷ ⊢w ⊢γ) fresh ⊢M eq
apply-pc≾ {γ = γ} {μ} {𝓁ᶜ = 𝓁ᶜ} {w = w} {k = k} 𝓁ᶜ≾𝓁₁ ⊢μ ⊢γ fresh
          (⊢ᵥproxy {S = S} {T} {S′} {T′} {v} {𝓁̂₁} {𝓁̂₂} {𝓁̂₁′} {𝓁̂₂′} {S′≲S} {T≲T′} {𝓁̂₁′≾𝓁̂₁} {𝓁̂₂≾𝓁̂₂′} ⊢v) ⊢w eq
  with castT μ 𝓁ᶜ S′ S w | castT-state-idem {μ} {𝓁ᶜ} {S′} {S} ⊢w | ⊢castT {μ} {𝓁ᶜ} {S′} {S} ⊢μ ⊢w
... | result ⟨ μ₁ , w′ , 𝓁ᶜ₁ ⟩ | ▹result μ≡μ₁ 𝓁ᶜ≡𝓁ᶜ₁ | ⊢ᵣresult ⊢μ₁ ⊢w′
  {- NOTE:
    In this step, we perform a cast ⟨ 𝓁̂₁′ ⇛ 𝓁̂₁ ⟩, and since it succeeds (otherwise is blamed and contradicts `eq`),
    we have 𝓁ᶜ ≾ 𝓁̂₁ .
  -}
  with castL μ₁ 𝓁ᶜ₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁
...   | result ⟨ μ₂ , _ , 𝓁ᶜ₂ ⟩
  with apply γ v w′ μ₂ 𝓁ᶜ₂ k
...     | result ⟨ μ₃ , v₁ , 𝓁ᶜ₃ ⟩
  with castL μ₃ 𝓁ᶜ₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′ | inspect (λ μ → castL μ 𝓁ᶜ₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′) μ₃ | castL-state-idem {μ₃} {𝓁ᶜ₃} 𝓁̂₂≾𝓁̂₂′
...       | result ⟨ μ₄ , _ , 𝓁ᶜ₄ ⟩ | [ eq₁ ] | ▹result _ 𝓁ᶜ₃≡𝓁ᶜ₄
  with castT μ₄ 𝓁ᶜ₄ T T′ v₁ | inspect (λ μ → castT μ 𝓁ᶜ₄ T T′ v₁) μ₄
...         | result ⟨ μ₅ , v₂ , 𝓁ᶜ₅ ⟩ | [ eq₂ ] =
  let 𝓁ᶜ₃≾𝓁̂₂′ = castL-no-blame-inv 𝓁̂₂≾𝓁̂₂′ eq₁ in
  let 𝓁ᶜ₄≡𝓁ᶜ₅ = castT→𝓁ᶜ≡ {μ₁ = μ₄} {𝓁ᶜ₁ = 𝓁ᶜ₄} {T₁ = T} {T′} v₁ eq₂ in
  let 𝓁ᶜ₅≡𝓁ᶜ′ = result≡→𝓁ᶜ≡ eq in
    subst (λ □ → l̂ □ ≾ _) (trans 𝓁ᶜ₃≡𝓁ᶜ₄ (trans 𝓁ᶜ₄≡𝓁ᶜ₅ 𝓁ᶜ₅≡𝓁ᶜ′)) 𝓁ᶜ₃≾𝓁̂₂′

𝒱-pres-pc≲ 0 _ _ _ _ _ ()
𝒱-pres-pc≲ {γ = γ} (suc k) 𝓁ᶜ₁≾𝓁₁ _ _ _ (⊢` {x = x} eq) eq₁
  with nth γ x
... | just _ rewrite sym (result≡→𝓁ᶜ≡ eq₁) = 𝓁ᶜ₁≾𝓁₁
𝒱-pres-pc≲ (suc k) 𝓁ᶜ₁≾𝓁₁ _ _ _ ⊢tt eq rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁
𝒱-pres-pc≲ (suc k) 𝓁ᶜ₁≾𝓁₁ _ _ _ ⊢true eq rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁
𝒱-pres-pc≲ (suc k) 𝓁ᶜ₁≾𝓁₁ _ _ _ ⊢false eq rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢let {T = T} {T′} {M = M} {N} {𝓁̂₁} {𝓁̂₂} {𝓁̂₃} ⊢M ⊢N T′≲T) eq
  with 𝒱 γ M ⊢M μ₁ 𝓁ᶜ₁ k
     | 𝒱-safe {Γ} k 𝓁ᶜ₁ ⊢μ₁ fresh ⊢γ ⊢M
     | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ₁} {𝓁ᶜ₁} {k} ⊢M ⊢μ₁ ⊢γ fresh
     | 𝒱-pres-⊢ₑ {pc = 𝓁ᶜ₁} {k} ⊢M ⊢μ₁ ⊢γ ⊢γ fresh
     | inspect (λ □ → 𝒱 γ M □ μ₁ 𝓁ᶜ₁ k) ⊢M
... | result ⟨ μ′ , v′ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | WFresult freshμ′ | WTenv-result μ′⊢γ | [ eq₁ ]
  with castT μ′ 𝓁ᶜ′ T′ T v′ | ⊢castT {μ′} {𝓁ᶜ′} {T′} {T} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {𝓁ᶜ′} {T′} {T} ⊢v′
...   | result ⟨ μ″ , v″ , 𝓁ᶜ″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ 𝓁ᶜ′≡𝓁ᶜ″ rewrite (sym μ′≡μ″) =
  let 𝓁ᶜ′≾𝓁₂ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let 𝓁ᶜ″≾𝓁₂ = subst (λ □ → l̂ □ ≾ 𝓁̂₂) 𝓁ᶜ′≡𝓁ᶜ″ 𝓁ᶜ′≾𝓁₂ in
    𝒱-pres-pc≲ k 𝓁ᶜ″≾𝓁₂ ⊢μ″ (⊢ₑ∷ ⊢v″ μ′⊢γ) freshμ′ ⊢N eq


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq
  with nth γ x
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq | just V-true
  with 𝒱 γ _ ⊢M μ₁ 𝓁ᶜ₁ k | 𝒱-safe {Γ} k 𝓁ᶜ₁ ⊢μ₁ fresh ⊢γ ⊢M | inspect (λ ⊢M → 𝒱 γ _ ⊢M μ₁ 𝓁ᶜ₁ k) ⊢M
... | result ⟨ μ′ , vₘ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | [ eq₁ ]
  with castL μ′ 𝓁ᶜ′ 𝓁̂₂ (𝓁̂₂ ⋎ 𝓁̂₂′) (𝓁̂≾𝓁̂⋎𝓁̂′ _ _) | castL-state-idem {μ′} {𝓁ᶜ′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} (𝓁̂≾𝓁̂⋎𝓁̂′ _ _)
...   | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | ▹result μ′≡μ″ 𝓁ᶜ′≡𝓁ᶜ″
  with castT μ″ 𝓁ᶜ″ T T″ vₘ | castT-state-idem {μ″} {𝓁ᶜ″} {T} {T″} μ″⊢vₘ
  where
  μ″⊢vₘ = subst (λ □ → □ ⊢ᵥ vₘ ⦂ _) μ′≡μ″ ⊢vₘ
...     | result _ | ▹result _ 𝓁ᶜ″≡𝓁ᶜ₂′ =
  let 𝓁ᶜ′≾𝓁₂ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let 𝓁ᶜ₂′≡𝓁ᶜ₂ = result≡→𝓁ᶜ≡ eq in
  let 𝓁ᶜ₂≾𝓁₂ = subst (λ □ → l̂ □ ≾ 𝓁̂₂) (trans 𝓁ᶜ′≡𝓁ᶜ″ (trans 𝓁ᶜ″≡𝓁ᶜ₂′ 𝓁ᶜ₂′≡𝓁ᶜ₂)) 𝓁ᶜ′≾𝓁₂ in
    𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ 𝓁ᶜ₂≾𝓁₂
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq | just V-false
  with 𝒱 γ _ ⊢N μ₁ 𝓁ᶜ₁ k | 𝒱-safe {Γ} k 𝓁ᶜ₁ ⊢μ₁ fresh ⊢γ ⊢N | inspect (λ ⊢N → 𝒱 γ _ ⊢N μ₁ 𝓁ᶜ₁ k) ⊢N
... | result ⟨ μ′ , vₙ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | [ eq₁ ]
  with castL μ′ 𝓁ᶜ′ 𝓁̂₂′ (𝓁̂₂ ⋎ 𝓁̂₂′) (𝓁̂≾𝓁̂′⋎𝓁̂ _ _) | castL-state-idem {μ′} {𝓁ᶜ′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} (𝓁̂≾𝓁̂′⋎𝓁̂ _ _)
...   | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | ▹result μ′≡μ″ 𝓁ᶜ′≡𝓁ᶜ″
  with castT μ″ 𝓁ᶜ″ T′ T″ vₙ | castT-state-idem {μ″} {𝓁ᶜ″} {T′} {T″} μ″⊢vₙ
  where
  μ″⊢vₙ = subst (λ □ → □ ⊢ᵥ vₙ ⦂ _) μ′≡μ″ ⊢vₙ
...     | result _ | ▹result _ 𝓁ᶜ″≡𝓁ᶜ₂′ =
  let 𝓁ᶜ′≾𝓁₂′ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢N eq₁ in
  let 𝓁ᶜ₂′≡𝓁ᶜ₂ = result≡→𝓁ᶜ≡ eq in
  let 𝓁ᶜ₂≾𝓁₂′ = subst (λ □ → l̂ □ ≾ 𝓁̂₂′) (trans 𝓁ᶜ′≡𝓁ᶜ″ (trans 𝓁ᶜ″≡𝓁ᶜ₂′ 𝓁ᶜ₂′≡𝓁ᶜ₂)) 𝓁ᶜ′≾𝓁₂′ in
    subst (λ □ → l̂ _ ≾ □) (⋎-comm 𝓁̂₂′ 𝓁̂₂) (𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ 𝓁ᶜ₂≾𝓁₂′)


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} {𝓁ᶜ₂} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢get {x = x} {T} {𝓁̂₁} eq₁) eq
  with nth γ x | inspect (λ γ → nth γ x) γ
... | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) | [ eq₂ ]
  with lookup μ₁ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ | inspect (λ μ → lookup μ ⟨ n , 𝓁₁ , 𝓁₂ ⟩) μ₁
...   | just ⟨ T′ , v ⟩ | [ eq₃ ]
  with castT μ₁ (𝓁ᶜ₁ ⊔ 𝓁₂) T′ T v | castT-state-idem {μ₁} {𝓁ᶜ₁ ⊔ 𝓁₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe ⊢μ₁ eq₃
...     | result _  | ▹result _ 𝓁ᶜ≡ with ⊢ₑ→nth⊢ᵥ ⊢γ eq₂ eq₁
...       | ⊢ᵥref {𝓁₂ = 𝓁₂} _ rewrite sym (trans 𝓁ᶜ≡ (result≡→𝓁ᶜ≡ eq)) = 𝓁₁≾𝓁̂→𝓁₁⊔𝓁₂≾𝓁̂⋎𝓁₂ 𝓁ᶜ₁≾𝓁₁
...       | ⊢ᵥref-dyn _ rewrite 𝓁̂⋎¿≡¿ 𝓁̂₁ = ≾-¿-r


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢set {x = x} {y} {T} {T′} _ _ _ _) eq
  with nth γ x | nth γ y
... | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) | just v
  with lookup μ₁ ⟨ n , 𝓁₁ , 𝓁₂ ⟩
...   | just ⟨ T″ , _ ⟩
  with castT μ₁ (𝓁ᶜ₁ ⊔ 𝓁₂) T′ T v
...     | result ⟨ μ′ , v′ , 𝓁ᶜ′ ⟩
  with castT μ′ 𝓁ᶜ′ T T″ v′
...       | result ⟨ μ″ , v″ , 𝓁ᶜ″ ⟩
  with 𝓁ᶜ″ ≼? 𝓁₂
...         | yes _ = {!!}


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢new {y = y} {𝓁 = 𝓁} _ _) eq
  with 𝓁ᶜ₁ ≼? 𝓁
... | yes _
  with nth γ y
...   | just v rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢new-dyn {x = x} {y} _ _) eq
  with nth γ x | nth γ y
... | just (V-label 𝓁) | just _
  with 𝓁ᶜ₁ ≼? 𝓁
...   | yes _ rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁


-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢eq-ref x x₁ x₂ x₃) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢ƛ tM) eq = {!!}


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁′ ⊢μ₁ ⊢γ fresh (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} eq₁ eq₂ _ 𝓁̂₁′≾𝓁̂₁) eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | v | ⊢v | w | ⊢w
  with castT μ₁ 𝓁ᶜ₁ T′ T w | ⊢castT {pc = 𝓁ᶜ₁} {T′} {T} ⊢μ₁ ⊢w | castT-state-idem {μ₁} {𝓁ᶜ₁} {T′} {T} ⊢w
...   | result ⟨ μ′ , w′ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢w′ | ▹result μ₁≡μ′ 𝓁ᶜ₁≡𝓁ᶜ′
  with castL μ′ 𝓁ᶜ′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ | inspect (λ μ → castL μ 𝓁ᶜ′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁) μ′
...     | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | [ eq₃ ]
  with apply γ v w′ μ₁ 𝓁ᶜ₁ k | inspect (λ γ → apply γ v w′ μ₁ 𝓁ᶜ₁ k) γ
...       | result _ | [ eq₄ ] rewrite (sym (result≡→𝓁ᶜ≡ eq)) =
  let 𝓁ᶜ₁≾𝓁₁ = subst (λ □ → l̂ □ ≾ _) (sym 𝓁ᶜ₁≡𝓁ᶜ′) (castL-no-blame-inv 𝓁̂₁′≾𝓁̂₁ eq₃) in
  let μ₁⊢w′ = subst (λ □ → □ ⊢ᵥ _ ⦂ _) (sym μ₁≡μ′) ⊢w′ in
    apply-pc≾ 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢v μ₁⊢w′ eq₄


-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢ref-label x) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢lab-label x) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ ⊢pc-label eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ ⊢label eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢≼ x x₁) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢⊔ x x₁) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢⊓ x x₁) eq = {!!}
-- -- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢unlabel x) eq = {!!}


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢to-label {M = M} {𝓁 = 𝓁} ⊢M _) eq
  with 𝒱 γ M ⊢M μ₁ 𝓁ᶜ₁ k
... | result ⟨ μ′ , v , 𝓁ᶜ′ ⟩
  with 𝓁ᶜ′ ≼? (𝓁ᶜ₁ ⊔ 𝓁)
...   | yes _ rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢to-label-dyn {x = x} {M = M} _ ⊢M) eq
  with nth γ x
... | just (V-label 𝓁)
  with 𝒱 γ M ⊢M μ₁ 𝓁ᶜ₁ k
...   | result ⟨ μ′ , v , 𝓁ᶜ′ ⟩
  with 𝓁ᶜ′ ≼? (𝓁ᶜ₁ ⊔ 𝓁)
...     | yes _ rewrite sym (result≡→𝓁ᶜ≡ eq) = 𝓁ᶜ₁≾𝓁₁
