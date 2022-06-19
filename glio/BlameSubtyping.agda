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
open import Lemmas
open import Interp
open import WellTypedness using (_⊢ᵥ_⦂_)
open import Store
open import WellTypedness
open import CastStateIdem
open import InterpSafe
open import Subtyping



-- CastL ℓ̂₁ ⇛ ℓ̂₂ never fails if ℓ̂₁ ≺: ℓ̂₂
≺:→no-blame : ∀ {μ pc ℓ̂₁ ℓ̂₂}
  → (l̂ pc) ≾ ℓ̂₁
  → (ℓ̂₁≺:ℓ̂₂ : ℓ̂₁ ≺: ℓ̂₂)
    --------------------------------------------------
  → castL μ pc ℓ̂₁ ℓ̂₂ (≺:→≾ ℓ̂₁≺:ℓ̂₂) ≡ result ⟨ μ , V-tt , pc ⟩
≺:→no-blame {pc = pc} {ℓ̂₁} {ℓ̂₂} pc≾ℓ₁ ℓ₁≺:ℓ₂
  with (l̂ pc) ≾? ℓ̂₂
... | yes pc≾ℓ₂ = refl
... | no pc⊀ℓ₂ = ⊥-elim (pc⊀ℓ₂ pc≾ℓ₂)
  where
  pc≾ℓ₂ = ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ pc≾ℓ₁ ℓ₁≺:ℓ₂


-- Cast T₁ ⇛ T₂ never fails if T₁ <: T₂
<:→no-blame : ∀ {μ pc T₁ T₂ v}
  → μ ⊢ᵥ v ⦂ T₁
  → (T₁<:T₂ : T₁ <: T₂)
    ------------------------------------------------------------------
  → ∃[ w ] (castT′ μ pc T₁ T₂ (<:→≲ T₁<:T₂) v ≡ result ⟨ μ , w , pc ⟩)
<:→no-blame ⊢ᵥtt <:-⊤ = ⟨ V-tt , refl ⟩
<:→no-blame ⊢ᵥtrue <:-𝔹 = ⟨ V-true , refl ⟩
<:→no-blame ⊢ᵥfalse <:-𝔹 = ⟨ V-false , refl ⟩
<:→no-blame ⊢ᵥlabel <:-ℒ = ⟨ V-label _ , refl ⟩
<:→no-blame (⊢ᵥref _) (<:-Ref ≂-¿ T₁≲T₂ T₂≲T₁) = ⟨ V-ref _ , refl ⟩
<:→no-blame (⊢ᵥref _) (<:-Ref {ℓ̂₂ = l̂ ℓ₂} ≂-l T₁≲T₂ T₂≲T₁)
  with ℓ₂ ≟ ℓ₂
... | yes _ = ⟨ V-ref _ , refl ⟩
... | no ℓ₂≢ℓ₂ = ⊥-elim (ℓ₂≢ℓ₂ refl)
<:→no-blame (⊢ᵥref-dyn _) (<:-Ref ≂-¿ T₁≲T₂ T₂≲T₁) = ⟨ V-ref _ , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab {ℓ = ℓ} ℓ≼ℓ′ ⊢v) (<:-Lab ≺:-¿ T₁<:T₂)
  with <:→no-blame {pc = pc} ⊢v T₁<:T₂
... | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab ℓ w , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab {ℓ = ℓ} ℓ≼ℓ′ ⊢v) (<:-Lab (≺:-l {ℓ₂ = ℓ₂} 𝓵′≼ℓ₂) T₁<:T₂)
  with ℓ ≼? ℓ₂
... | no ℓ⊀ℓ₂ = ⊥-elim (ℓ⊀ℓ₂ ℓ≼ℓ₂)
  where
  ℓ≼ℓ₂ = ≼-trans ℓ≼ℓ′ 𝓵′≼ℓ₂
... | yes _ with <:→no-blame {pc = pc} ⊢v T₁<:T₂
...   | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab ℓ w , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab-dyn ⊢v) (<:-Lab ≺:-¿ T₁<:T₂) with <:→no-blame {pc = pc} ⊢v T₁<:T₂
... | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab _ w , refl ⟩
<:→no-blame (⊢ᵥclos _ _) (<:-⇒ _ _ _ _) = ⟨ V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _ , refl ⟩
<:→no-blame (⊢ᵥproxy _) (<:-⇒ _ _ _ _) = ⟨ V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _ , refl ⟩



private
  timeout≢result : ∀ {conf : Conf} → timeout ≢ result conf
  timeout≢result ()

  error≢result : ∀ {err} {conf : Conf} → error err ≢ result conf
  error≢result ()

  result≡→ℓᶜ≡ : ∀ {μ₁ μ₂ : Store} {v₁ v₂ : Value} {ℓᶜ₁ ℓᶜ₂ : ℒ}
    → result ⟨ μ₁ , v₁ , ℓᶜ₁ ⟩ ≡ result ⟨ μ₂ , v₂ , ℓᶜ₂ ⟩
    → ℓᶜ₁ ≡ ℓᶜ₂
  result≡→ℓᶜ≡ res≡ =
    let conf₁≡conf₂ = result-≡-inv res≡ in
    let cdr₁≡cdr₂ = proj₂ (×-≡-inv conf₁≡conf₂) in
      proj₂ (×-≡-inv cdr₁≡cdr₂)

  castL→ℓᶜ≡ : ∀ {μ₁ μ₂ ℓᶜ₁ ℓᶜ₂ ℓ̂₁ ℓ̂₂ v}
    → (ℓ̂₁≾ℓ̂₂ : ℓ̂₁ ≾ ℓ̂₂)
    → castL μ₁ ℓᶜ₁ ℓ̂₁ ℓ̂₂ ℓ̂₁≾ℓ̂₂ ≡ result ⟨ μ₂ , v , ℓᶜ₂ ⟩
    → ℓᶜ₁ ≡ ℓᶜ₂
  castL→ℓᶜ≡ {ℓᶜ₁ = ℓᶜ₁} {ℓ̂₁ = ℓ̂₁} {ℓ̂₂} ℓ₁≾ℓ₂ eq with (l̂ ℓᶜ₁) ≾? ℓ̂₂
  ... | yes _ = result≡→ℓᶜ≡ eq
  ... | no  _ = ⊥-elim (error≢result eq)

  castT′→ℓᶜ≡ : ∀ {μ₁ μ₂ ℓᶜ₁ ℓᶜ₂ v₂ T₁ T₂}
    → (T₁≲T₂ : T₁ ≲ T₂)
    → (v₁ : Value)
    → castT′ μ₁ ℓᶜ₁ T₁ T₂ T₁≲T₂ v₁ ≡ result ⟨ μ₂ , v₂ , ℓᶜ₂ ⟩
    → ℓᶜ₁ ≡ ℓᶜ₂
  castT′→ℓᶜ≡ ≲-⊤ V-tt eq = result≡→ℓᶜ≡ eq
  castT′→ℓᶜ≡ ≲-𝔹 V-true eq = result≡→ℓᶜ≡ eq
  castT′→ℓᶜ≡ ≲-𝔹 V-false eq = result≡→ℓᶜ≡ eq
  castT′→ℓᶜ≡ ≲-ℒ (V-label _) eq = result≡→ℓᶜ≡ eq
  castT′→ℓᶜ≡ (≲-Ref {ℓ̂₂ = ℓ̂₂} _ _ _ _) (V-ref ⟨ _ , _ , ℓ₂ ⟩) eq with ℓ̂₂
  ... | ¿ = result≡→ℓᶜ≡ eq
  ... | (l̂ ℓ₂′) with ℓ₂ ≟ ℓ₂′
  ...   | yes _ = result≡→ℓᶜ≡ eq
  ...   | no  _ = ⊥-elim (error≢result eq)
  castT′→ℓᶜ≡ {μ₁} {μ₂} {ℓᶜ₁} (≲-Lab {ℓ̂₂ = ℓ̂₂} _ T₁≲T₂) (V-lab ℓ v) eq with (l̂ ℓ) ≾? ℓ̂₂
  ... | no _ = ⊥-elim (error≢result eq)
  ... | yes _ with castT′ μ₁ ℓᶜ₁ _ _ T₁≲T₂ v | inspect (λ v → castT′ μ₁ ℓᶜ₁ _ _ T₁≲T₂ v) v
  ...   | result ⟨ μ′ , v′ , ℓᶜ′ ⟩ | [ eq₁ ] =
    let ℓᶜ₁≡ℓᶜ′ = castT′→ℓᶜ≡ T₁≲T₂ v eq₁ in
    let ℓᶜ′≡ℓᶜ₂ = result≡→ℓᶜ≡ eq in
      trans ℓᶜ₁≡ℓᶜ′ ℓᶜ′≡ℓᶜ₂
  ...   | error err | _ = ⊥-elim (error≢result eq)
  ...   | timeout | _ = ⊥-elim (timeout≢result eq)
  castT′→ℓᶜ≡ (≲-⇒ _ _ _ _) (V-clos _) eq = result≡→ℓᶜ≡ eq
  castT′→ℓᶜ≡ (≲-⇒ _ _ _ _) (V-proxy _ _ _ _ _ _ _ _  _ _ _ _ _) eq = result≡→ℓᶜ≡ eq

  castT→ℓᶜ≡ : ∀ {μ₁ μ₂ ℓᶜ₁ ℓᶜ₂ v₂ T₁ T₂}
    → (v₁ : Value)
    → castT μ₁ ℓᶜ₁ T₁ T₂ v₁ ≡ result ⟨ μ₂ , v₂ , ℓᶜ₂ ⟩
    → ℓᶜ₁ ≡ ℓᶜ₂
  castT→ℓᶜ≡ {T₁ = T₁} {T₂} v₁ eq with T₁ ≲? T₂
  ... | yes T₁≲T₂ = castT′→ℓᶜ≡ T₁≲T₂ v₁ eq
  ... | no _ = ⊥-elim (error≢result eq)

  castL-no-blame-inv : ∀ {μ μ′ ℓ̂₁ ℓ̂₂ ℓᶜ ℓᶜ′ v}
    → (ℓ̂₁≾ℓ̂₂ : ℓ̂₁ ≾ ℓ̂₂)
    → castL μ ℓᶜ ℓ̂₁ ℓ̂₂ ℓ̂₁≾ℓ̂₂ ≡ result ⟨ μ′ , v , ℓᶜ′ ⟩
    → (l̂ ℓᶜ) ≾ ℓ̂₂
  castL-no-blame-inv {ℓ̂₂ = ℓ̂₂} {ℓᶜ = ℓᶜ} _ eq with (l̂ ℓᶜ) ≾? ℓ̂₂
  ... | yes ℓᶜ≾ℓ₂ = ℓᶜ≾ℓ₂


apply-pc≾ : ∀ {Γ γ μ μ′ T S ℓ̂₁ ℓ̂₂ ℓᶜ ℓᶜ′ v w v′ k}
  → (l̂ ℓᶜ) ≾ ℓ̂₁
  → μ ⊢ₛ μ
  → Γ ∣ μ ⊢ₑ γ
  → length μ ∉domₙ μ
  → μ ⊢ᵥ v ⦂ T [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S
  → μ ⊢ᵥ w ⦂ T
  → apply γ v w μ ℓᶜ k ≡ result ⟨ μ′ , v′ , ℓᶜ′ ⟩
  → (l̂ ℓᶜ′) ≾ ℓ̂₂

𝒱-pres-pc≲ : ∀ {Γ γ μ₁ μ₂ ℓᶜ₁ ℓᶜ₂ ℓ̂₁ ℓ̂₂ M v T}
  → (k : ℕ)
  → (l̂ ℓᶜ₁) ≾ ℓ̂₁
  → μ₁ ⊢ₛ μ₁
  → Γ ∣ μ₁ ⊢ₑ γ
  → length μ₁ ∉domₙ μ₁
  → (⊢M : Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T)
  → 𝒱 γ M ⊢M μ₁ ℓᶜ₁ k ≡ result ⟨ μ₂ , v , ℓᶜ₂ ⟩
    -------------------------------------------
  → (l̂ ℓᶜ₂) ≾ ℓ̂₂

apply-pc≾ {k = k} ℓᶜ≾ℓ₁ ⊢μ _ fresh (⊢ᵥclos ⊢γ ⊢M) ⊢w eq = 𝒱-pres-pc≲ k ℓᶜ≾ℓ₁ ⊢μ (⊢ₑ∷ ⊢w ⊢γ) fresh ⊢M eq
apply-pc≾ {γ = γ} {μ} {ℓᶜ = ℓᶜ} {w = w} {k = k} ℓᶜ≾ℓ₁ ⊢μ ⊢γ fresh
          (⊢ᵥproxy {S = S} {T} {S′} {T′} {v} {ℓ̂₁} {ℓ̂₂} {ℓ̂₁′} {ℓ̂₂′} {S′≲S} {T≲T′} {ℓ̂₁′≾ℓ̂₁} {ℓ̂₂≾ℓ̂₂′} ⊢v) ⊢w eq
  with castT μ ℓᶜ S′ S w | castT-state-idem {μ} {ℓᶜ} {S′} {S} ⊢w | ⊢castT {μ} {ℓᶜ} {S′} {S} ⊢μ ⊢w
... | result ⟨ μ₁ , w′ , ℓᶜ₁ ⟩ | ▹result μ≡μ₁ ℓᶜ≡ℓᶜ₁ | ⊢ᵣresult ⊢μ₁ ⊢w′
  {- NOTE:
    In this step, we perform a cast ⟨ ℓ̂₁′ ⇛ ℓ̂₁ ⟩, and since it succeeds (otherwise is blamed and contradicts `eq`),
    we have ℓᶜ ≾ ℓ̂₁ .
  -}
  with castL μ₁ ℓᶜ₁ ℓ̂₁′ ℓ̂₁ ℓ̂₁′≾ℓ̂₁
...   | result ⟨ μ₂ , _ , ℓᶜ₂ ⟩
  with apply γ v w′ μ₂ ℓᶜ₂ k
...     | result ⟨ μ₃ , v₁ , ℓᶜ₃ ⟩
  with castL μ₃ ℓᶜ₃ ℓ̂₂ ℓ̂₂′ ℓ̂₂≾ℓ̂₂′ | inspect (λ μ → castL μ ℓᶜ₃ ℓ̂₂ ℓ̂₂′ ℓ̂₂≾ℓ̂₂′) μ₃ | castL-state-idem {μ₃} {ℓᶜ₃} ℓ̂₂≾ℓ̂₂′
...       | result ⟨ μ₄ , _ , ℓᶜ₄ ⟩ | [ eq₁ ] | ▹result _ ℓᶜ₃≡ℓᶜ₄
  with castT μ₄ ℓᶜ₄ T T′ v₁ | inspect (λ μ → castT μ ℓᶜ₄ T T′ v₁) μ₄
...         | result ⟨ μ₅ , v₂ , ℓᶜ₅ ⟩ | [ eq₂ ] =
  let ℓᶜ₃≾ℓ̂₂′ = castL-no-blame-inv ℓ̂₂≾ℓ̂₂′ eq₁ in
  let ℓᶜ₄≡ℓᶜ₅ = castT→ℓᶜ≡ {μ₁ = μ₄} {ℓᶜ₁ = ℓᶜ₄} {T₁ = T} {T′} v₁ eq₂ in
  let ℓᶜ₅≡ℓᶜ′ = result≡→ℓᶜ≡ eq in
    subst (λ □ → l̂ □ ≾ _) (trans ℓᶜ₃≡ℓᶜ₄ (trans ℓᶜ₄≡ℓᶜ₅ ℓᶜ₅≡ℓᶜ′)) ℓᶜ₃≾ℓ̂₂′


𝒱-pres-pc≲ 0 _ _ _ _ _ ()
𝒱-pres-pc≲ {γ = γ} (suc k) ℓᶜ₁≾ℓ₁ _ _ _ (⊢` {x = x} eq) eq₁
  with nth γ x
... | just _ rewrite sym (result≡→ℓᶜ≡ eq₁) = ℓᶜ₁≾ℓ₁
𝒱-pres-pc≲ (suc k) ℓᶜ₁≾ℓ₁ _ _ _ ⊢tt eq rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁
𝒱-pres-pc≲ (suc k) ℓᶜ₁≾ℓ₁ _ _ _ ⊢true eq rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁
𝒱-pres-pc≲ (suc k) ℓᶜ₁≾ℓ₁ _ _ _ ⊢false eq rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢let {T = T} {T′} {M = M} {N} {ℓ̂₁} {ℓ̂₂} {ℓ̂₃} ⊢M ⊢N T′≲T) eq
  with 𝒱 γ M ⊢M μ₁ ℓᶜ₁ k
     | 𝒱-safe {Γ} k ℓᶜ₁ ⊢μ₁ fresh ⊢γ ⊢M
     | 𝒱-pres-WFaddr {Γ} {γ} {μ = μ₁} {ℓᶜ₁} {k} ⊢M ⊢μ₁ ⊢γ fresh
     | 𝒱-pres-⊢ₑ {pc = ℓᶜ₁} {k} ⊢M ⊢μ₁ ⊢γ ⊢γ fresh
     | inspect (λ □ → 𝒱 γ M □ μ₁ ℓᶜ₁ k) ⊢M
... | result ⟨ μ′ , v′ , ℓᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | WFresult freshμ′ | WTenv-result μ′⊢γ | [ eq₁ ]
  with castT μ′ ℓᶜ′ T′ T v′ | ⊢castT {μ′} {ℓᶜ′} {T′} {T} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {ℓᶜ′} {T′} {T} ⊢v′
...   | result ⟨ μ″ , v″ , ℓᶜ″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ ℓᶜ′≡ℓᶜ″ rewrite (sym μ′≡μ″) =
  let ℓᶜ′≾ℓ₂ = 𝒱-pres-pc≲ k ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let ℓᶜ″≾ℓ₂ = subst (λ □ → l̂ □ ≾ ℓ̂₂) ℓᶜ′≡ℓᶜ″ ℓᶜ′≾ℓ₂ in
    𝒱-pres-pc≲ k ℓᶜ″≾ℓ₂ ⊢μ″ (⊢ₑ∷ ⊢v″ μ′⊢γ) freshμ′ ⊢N eq

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {ℓ̂₂ = ℓ̂₂} {ℓ̂₂′} _ ⊢M ⊢N _) eq
  with nth γ x
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {ℓ̂₂ = ℓ̂₂} {ℓ̂₂′} _ ⊢M ⊢N _) eq | just V-true
  with 𝒱 γ _ ⊢M μ₁ ℓᶜ₁ k | 𝒱-safe {Γ} k ℓᶜ₁ ⊢μ₁ fresh ⊢γ ⊢M | inspect (λ ⊢M → 𝒱 γ _ ⊢M μ₁ ℓᶜ₁ k) ⊢M
... | result ⟨ μ′ , vₘ , ℓᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | [ eq₁ ]
  with castL μ′ ℓᶜ′ ℓ̂₂ (ℓ̂₂ ⋎ ℓ̂₂′) (ℓ̂≾ℓ̂⋎ℓ̂′ _ _) | castL-state-idem {μ′} {ℓᶜ′} {ℓ̂₂} {ℓ̂₂ ⋎ ℓ̂₂′} (ℓ̂≾ℓ̂⋎ℓ̂′ _ _)
...   | result ⟨ μ″ , _ , ℓᶜ″ ⟩ | ▹result μ′≡μ″ ℓᶜ′≡ℓᶜ″
  with castT μ″ ℓᶜ″ T T″ vₘ | castT-state-idem {μ″} {ℓᶜ″} {T} {T″} μ″⊢vₘ
  where
  μ″⊢vₘ = subst (λ □ → □ ⊢ᵥ vₘ ⦂ _) μ′≡μ″ ⊢vₘ
...     | result _ | ▹result _ ℓᶜ″≡ℓᶜ₂′ =
  let ℓᶜ′≾ℓ₂ = 𝒱-pres-pc≲ k ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let ℓᶜ₂′≡ℓᶜ₂ = result≡→ℓᶜ≡ eq in
  let ℓᶜ₂≾ℓ₂ = subst (λ □ → l̂ □ ≾ ℓ̂₂) (trans ℓᶜ′≡ℓᶜ″ (trans ℓᶜ″≡ℓᶜ₂′ ℓᶜ₂′≡ℓᶜ₂)) ℓᶜ′≾ℓ₂ in
    ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ ℓᶜ₂≾ℓ₂
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} {T = T} {T′} {T″} {ℓ̂₂ = ℓ̂₂} {ℓ̂₂′} _ ⊢M ⊢N _) eq | just V-false
  with 𝒱 γ _ ⊢N μ₁ ℓᶜ₁ k | 𝒱-safe {Γ} k ℓᶜ₁ ⊢μ₁ fresh ⊢γ ⊢N | inspect (λ ⊢N → 𝒱 γ _ ⊢N μ₁ ℓᶜ₁ k) ⊢N
... | result ⟨ μ′ , vₙ , ℓᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | [ eq₁ ]
  with castL μ′ ℓᶜ′ ℓ̂₂′ (ℓ̂₂ ⋎ ℓ̂₂′) (ℓ̂≾ℓ̂′⋎ℓ̂ _ _) | castL-state-idem {μ′} {ℓᶜ′} {ℓ̂₂′} {ℓ̂₂ ⋎ ℓ̂₂′} (ℓ̂≾ℓ̂′⋎ℓ̂ _ _)
...   | result ⟨ μ″ , _ , ℓᶜ″ ⟩ | ▹result μ′≡μ″ ℓᶜ′≡ℓᶜ″
  with castT μ″ ℓᶜ″ T′ T″ vₙ | castT-state-idem {μ″} {ℓᶜ″} {T′} {T″} μ″⊢vₙ
  where
  μ″⊢vₙ = subst (λ □ → □ ⊢ᵥ vₙ ⦂ _) μ′≡μ″ ⊢vₙ
...     | result _ | ▹result _ ℓᶜ″≡ℓᶜ₂′ =
  let ℓᶜ′≾ℓ₂′ = 𝒱-pres-pc≲ k ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢N eq₁ in
  let ℓᶜ₂′≡ℓᶜ₂ = result≡→ℓᶜ≡ eq in
  let ℓᶜ₂≾ℓ₂′ = subst (λ □ → l̂ □ ≾ ℓ̂₂′) (trans ℓᶜ′≡ℓᶜ″ (trans ℓᶜ″≡ℓᶜ₂′ ℓᶜ₂′≡ℓᶜ₂)) ℓᶜ′≾ℓ₂′ in
    subst (λ □ → l̂ _ ≾ □) (⋎-comm ℓ̂₂′ ℓ̂₂) (ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ ℓᶜ₂≾ℓ₂′)

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} {ℓᶜ₂} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢get {x = x} {T} {ℓ̂₁} eq₁) eq
  with nth γ x | inspect (λ γ → nth γ x) γ
... | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) | [ eq₂ ]
  with lookup μ₁ ⟨ n , ℓ₁ , ℓ₂ ⟩ | inspect (λ μ → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩) μ₁
...   | just ⟨ T′ , v ⟩ | [ eq₃ ]
  with castT μ₁ (ℓᶜ₁ ⊔ ℓ₂) T′ T v | castT-state-idem {μ₁} {ℓᶜ₁ ⊔ ℓ₂} {T′} {T} ⊢v
  where
  ⊢v = lookup-safe ⊢μ₁ eq₃
...     | result _  | ▹result _ ℓᶜ≡ with ⊢ₑ→nth⊢ᵥ ⊢γ eq₂ eq₁
...       | ⊢ᵥref {ℓ₂ = ℓ₂} _ rewrite sym (trans ℓᶜ≡ (result≡→ℓᶜ≡ eq)) = ℓ₁≾ℓ̂→ℓ₁⊔ℓ₂≾ℓ̂⋎ℓ₂ ℓᶜ₁≾ℓ₁
...       | ⊢ᵥref-dyn _ rewrite ℓ̂⋎¿≡¿ ℓ̂₁ = ≾-¿-r

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢set {x = x} {y} {T} {T′} _ _ _ _) eq
  with nth γ x | nth γ y
... | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) | just v
  with lookup μ₁ ⟨ n , ℓ₁ , ℓ₂ ⟩
...   | just ⟨ T″ , _ ⟩
  {- NOTE:
    Since we don't upgrade ℓᶜ with the join of ℓ₂ in the operational semantics anymore,
    the case-split here is updated accordingly.
  -}
  with castT μ₁ ℓᶜ₁ T′ T v | inspect (λ μ → castT μ ℓᶜ₁ T′ T v) μ₁
...     | result ⟨ μ′ , v′ , ℓᶜ′ ⟩ | [ eq₁ ]
  with castT μ′ ℓᶜ′ T T″ v′ | inspect (λ μ → castT μ ℓᶜ′ T T″ v′) μ′
...       | result ⟨ μ″ , v″ , ℓᶜ″ ⟩ | [ eq₂ ]
  with ℓᶜ″ ≼? ℓ₂
...         | yes _ rewrite sym (result≡→ℓᶜ≡ eq) =
  let ℓᶜ₁≡ℓᶜ′ = castT→ℓᶜ≡ {μ₁ = μ₁} {ℓᶜ₁ = ℓᶜ₁} {T₁ = T′} {T} v eq₁ in
  let ℓᶜ′≡ℓᶜ″ = castT→ℓᶜ≡ {μ₁ = μ′} {ℓᶜ₁ = ℓᶜ′} {T₁ = T} {T″} v′ eq₂ in
    subst (λ □ → l̂ □ ≾ _) (trans ℓᶜ₁≡ℓᶜ′ ℓᶜ′≡ℓᶜ″) ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢new {y = y} {ℓ = ℓ} _ _) eq
  with ℓᶜ₁ ≼? ℓ
... | yes _
  with nth γ y
...   | just v rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢new-dyn {x = x} {y} _ _) eq
  with nth γ x | nth γ y
... | just (V-label ℓ) | just _
  with ℓᶜ₁ ≼? ℓ
...   | yes _ rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢eq-ref {x = x} {y} _ _ _ _) eq
  with nth γ x | nth γ y
... | just (V-ref loc) | just (V-ref loc′) rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢ƛ _) eq rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁′ ⊢μ₁ ⊢γ fresh (⊢· {x = x} {y} {T} {T′} {S} {ℓ̂₁} {ℓ̂₁′} eq₁ eq₂ _ ℓ̂₁′≾ℓ̂₁) eq
  rewrite proj₂ (⊢γ→∃v ⊢γ eq₁) | proj₂ (⊢γ→∃v ⊢γ eq₂)
  with proj₁ (⊢γ→∃v ⊢γ eq₁) | (⊢γ→⊢v ⊢γ eq₁) | proj₁ (⊢γ→∃v ⊢γ eq₂) | (⊢γ→⊢v ⊢γ eq₂)
... | v | ⊢v | w | ⊢w
  with castT μ₁ ℓᶜ₁ T′ T w | ⊢castT {pc = ℓᶜ₁} {T′} {T} ⊢μ₁ ⊢w | castT-state-idem {μ₁} {ℓᶜ₁} {T′} {T} ⊢w
...   | result ⟨ μ′ , w′ , ℓᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢w′ | ▹result μ₁≡μ′ ℓᶜ₁≡ℓᶜ′
  with castL μ′ ℓᶜ′ ℓ̂₁′ ℓ̂₁ ℓ̂₁′≾ℓ̂₁ | inspect (λ μ → castL μ ℓᶜ′ ℓ̂₁′ ℓ̂₁ ℓ̂₁′≾ℓ̂₁) μ′
...     | result ⟨ μ″ , _ , ℓᶜ″ ⟩ | [ eq₃ ]
  with apply γ v w′ μ₁ ℓᶜ₁ k | inspect (λ γ → apply γ v w′ μ₁ ℓᶜ₁ k) γ
...       | result _ | [ eq₄ ] rewrite (sym (result≡→ℓᶜ≡ eq)) =
  let ℓᶜ₁≾ℓ₁ = subst (λ □ → l̂ □ ≾ _) (sym ℓᶜ₁≡ℓᶜ′) (castL-no-blame-inv ℓ̂₁′≾ℓ̂₁ eq₃) in
  let μ₁⊢w′ = subst (λ □ → □ ⊢ᵥ _ ⦂ _) (sym μ₁≡μ′) ⊢w′ in
    apply-pc≾ ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢v μ₁⊢w′ eq₄

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢ref-label {x = x} _) eq
  with nth γ x
... | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢lab-label {x = x} _) eq
  with nth γ x
... | just (V-lab ℓ v) rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢pc-label eq rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh ⊢label eq rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢≼ {x = x} {y} _ _) eq
  with nth γ x | nth γ y
... | just (V-label ℓˣ) | just (V-label ℓʸ) with ℓˣ ≼? ℓʸ
...   | yes _ rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁
...   | no  _ rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢⊔ {x = x} {y} _ _) eq
  with nth γ x | nth γ y
... | just (V-label _ ) | just (V-label _) rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢⊓ {x = x} {y} _ _) eq
  with nth γ x | nth γ y
... | just (V-label _) | just (V-label _) rewrite result≡→ℓᶜ≡ eq = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} {ℓᶜ₂} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢unlabel {x = x} {ℓ̂₁ = ℓ̂₁} eq₁) eq
  with nth γ x | inspect (λ γ → nth γ x) γ
... | just (V-lab ℓ _) | [ eq₂ ]
  with ⊢ₑ→nth⊢ᵥ ⊢γ eq₂ eq₁
...   | ⊢ᵥlab ℓ≼ℓ′ _ rewrite sym (result≡→ℓᶜ≡ eq) = ℓ≾ℓ̂→ℓ₁≼ℓ₂→ℓ⊔ℓ₁≾ℓ̂⋎ℓ₂ ℓᶜ₁≾ℓ₁ ℓ≼ℓ′
...   | ⊢ᵥlab-dyn _ rewrite sym (result≡→ℓᶜ≡ eq) | ℓ̂⋎¿≡¿ ℓ̂₁ = ≾-¿-r

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢to-label {M = M} {ℓ = ℓ} ⊢M _) eq
  with 𝒱 γ M ⊢M μ₁ ℓᶜ₁ k
... | result ⟨ μ′ , v , ℓᶜ′ ⟩
  with ℓᶜ′ ≼? (ℓᶜ₁ ⊔ ℓ)
...   | yes _ rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁

𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {ℓᶜ₁} (suc k) ℓᶜ₁≾ℓ₁ ⊢μ₁ ⊢γ fresh (⊢to-label-dyn {x = x} {M = M} _ ⊢M) eq
  with nth γ x
... | just (V-label ℓ)
  with 𝒱 γ M ⊢M μ₁ ℓᶜ₁ k
...   | result ⟨ μ′ , v , ℓᶜ′ ⟩
  with ℓᶜ′ ≼? (ℓᶜ₁ ⊔ ℓ)
...     | yes _ rewrite sym (result≡→ℓᶜ≡ eq) = ℓᶜ₁≾ℓ₁
