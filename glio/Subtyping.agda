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



infixl 9 _≺:_

data _≺:_ : ℒ̂ → ℒ̂ → Set where

  ≺:-¿ : ∀ {𝓁̂}
       ------
    → 𝓁̂ ≺: ¿

  ≺:-l : ∀ {𝓁₁ 𝓁₂}
    → 𝓁₁ ≼ 𝓁₂
      -----------------
    → (l̂ 𝓁₁) ≺: (l̂ 𝓁₂)



𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ : ∀ {𝓁 𝓁̂₁}
  → (𝓁̂₂ : ℒ̂)
  → (l̂ 𝓁) ≾ 𝓁̂₁
    -----------------
  → (l̂ 𝓁) ≺: 𝓁̂₁ ⋎ 𝓁̂₂
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {𝓁̂₁} ¿ 𝓁≾𝓁₁ rewrite 𝓁̂⋎¿≡¿ 𝓁̂₁ = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {¿} (l̂ _) _ = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {l̂ 𝓁₁} (l̂ 𝓁₂) (≾-l 𝓁≼𝓁₁) = ≺:-l (𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ 𝓁₂ 𝓁≼𝓁₁)

𝓁≺:𝓁⋎𝓁′ : ∀ 𝓁̂ 𝓁̂′ → 𝓁̂ ≺: 𝓁̂ ⋎ 𝓁̂′
𝓁≺:𝓁⋎𝓁′ 𝓁̂ ¿ rewrite 𝓁̂⋎¿≡¿ 𝓁̂ = ≺:-¿
𝓁≺:𝓁⋎𝓁′ ¿ (l̂ 𝓁′) = ≺:-¿
𝓁≺:𝓁⋎𝓁′ (l̂ 𝓁) (l̂ 𝓁′) = ≺:-l (𝓁≼𝓁⊔𝓁′ 𝓁 𝓁′)

-- ≺: is smaller than ≾
≺:→≾ : ∀ {𝓁 𝓁′}
  → 𝓁 ≺: 𝓁′
    --------
  → 𝓁 ≾ 𝓁′
≺:→≾ ≺:-¿ = ≾-¿-r
≺:→≾ (≺:-l 𝓁₁≼𝓁₂) = ≾-l 𝓁₁≼𝓁₂

-- Consistent subtyping ≾ is not transitive; alternatively, we have:
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₃}
  → 𝓁̂₁ ≾ 𝓁̂₂
  → 𝓁̂₂ ≺: 𝓁̂₃
    ---------
  → 𝓁̂₁ ≾ 𝓁̂₃
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-r ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-l ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ (≾-l _) ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-l (≺:-l _) = ≾-¿-l
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ {l̂ 𝓁₁} {l̂ 𝓁₂} {l̂ 𝓁₃} (≾-l 𝓁₁≼𝓁₂) (≺:-l 𝓁₂≼𝓁₃) = ≾-l (≼-trans 𝓁₁≼𝓁₂ 𝓁₂≼𝓁₃)

-- CastL 𝓁̂₁ ⇛ 𝓁̂₂ never fails if 𝓁̂₁ ≺: 𝓁̂₂
≺:→no-blame : ∀ {μ pc 𝓁̂₁ 𝓁̂₂}
  → (l̂ pc) ≾ 𝓁̂₁
  → (𝓁̂₁≺:𝓁̂₂ : 𝓁̂₁ ≺: 𝓁̂₂)
    --------------------------------------------------
  → castL μ pc 𝓁̂₁ 𝓁̂₂ (≺:→≾ 𝓁̂₁≺:𝓁̂₂) ≡ result ⟨ μ , V-tt , pc ⟩
≺:→no-blame {pc = pc} {𝓁̂₁} {𝓁̂₂} pc≾𝓁₁ 𝓁₁≺:𝓁₂
  with (l̂ pc) ≾? 𝓁̂₂
... | yes pc≾𝓁₂ = refl
... | no pc⊀𝓁₂ = ⊥-elim (pc⊀𝓁₂ pc≾𝓁₂)
  where
  pc≾𝓁₂ = 𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ pc≾𝓁₁ 𝓁₁≺:𝓁₂



infixl 9 _≂_

data _≂_ : ℒ̂ → ℒ̂ → Set where

  ≂-¿ : ∀ {𝓁̂}
      ------
    → 𝓁̂ ≂ ¿

  ≂-l : ∀ {𝓁}
      ---------------
    → (l̂ 𝓁) ≂ (l̂ 𝓁)

infixl 9 _<:_

data _<:_ : 𝕋 → 𝕋 → Set where

  <:-⊤ : `⊤ <: `⊤

  <:-𝔹 : `𝔹 <: `𝔹

  <:-ℒ : `ℒ <: `ℒ

  <:-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ≂ 𝓁̂₂
    → T₁ ≲ T₂ → T₂ ≲ T₁
      -----------------------
    → Ref 𝓁̂₁ T₁ <: Ref 𝓁̂₂ T₂

  <:-Lab : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ≺: 𝓁̂₂
    → T₁ <: T₂
      -----------------------
    → Lab 𝓁̂₁ T₁ <: Lab 𝓁̂₂ T₂

  <:-⇒ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S₁ S₂ T₁ T₂}
    → 𝓁̂₁′ ≺: 𝓁̂₁
    → 𝓁̂₂ ≺: 𝓁̂₂′
    → T₁ <: S₁
    → S₂ <: T₂
      ---------------------------------------------------
    → (S₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S₂) <: (T₁ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂)



≂→≾ : ∀ {𝓁̂₁ 𝓁̂₂}
  → 𝓁̂₁ ≂ 𝓁̂₂
    ------------------
  → 𝓁̂₁ ≾ 𝓁̂₂ × 𝓁̂₂ ≾ 𝓁̂₁
≂→≾ ≂-¿ = ⟨ ≾-¿-r , ≾-¿-l ⟩
≂→≾ ≂-l = ⟨ ≾-refl _ , ≾-refl _ ⟩

-- <: is smaller than ≲
<:→≲ : ∀ {T₁ T₂}
  → T₁ <: T₂
    ----------
  → T₁ ≲ T₂
<:→≲ <:-⊤ = ≲-⊤
<:→≲ <:-𝔹 = ≲-𝔹
<:→≲ <:-ℒ = ≲-ℒ
<:→≲ (<:-Ref 𝓁₁≂𝓁₂ T₁≲T₂ T₂≲T₁) =
  let ⟨ 𝓁₁≾𝓁₂ , 𝓁₂≾𝓁₁ ⟩ = ≂→≾ 𝓁₁≂𝓁₂ in
    ≲-Ref 𝓁₁≾𝓁₂ 𝓁₂≾𝓁₁ T₁≲T₂ T₂≲T₁
<:→≲ (<:-Lab 𝓁₁≺:𝓁₂ T₁<:T₂) = ≲-Lab (≺:→≾ 𝓁₁≺:𝓁₂) (<:→≲ T₁<:T₂)
<:→≲ (<:-⇒ 𝓁₁′≺:𝓁₁ 𝓁₂≺:𝓁₂′ T₁<:S₁ S₂<:T₂) = ≲-⇒ (≺:→≾ 𝓁₁′≺:𝓁₁) (≺:→≾ 𝓁₂≺:𝓁₂′) (<:→≲ T₁<:S₁) (<:→≲ S₂<:T₂)

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
<:→no-blame (⊢ᵥref _) (<:-Ref {𝓁̂₂ = l̂ 𝓁₂} ≂-l T₁≲T₂ T₂≲T₁)
  with 𝓁₂ ≟ 𝓁₂
... | yes _ = ⟨ V-ref _ , refl ⟩
... | no 𝓁₂≢𝓁₂ = ⊥-elim (𝓁₂≢𝓁₂ refl)
<:→no-blame (⊢ᵥref-dyn _) (<:-Ref ≂-¿ T₁≲T₂ T₂≲T₁) = ⟨ V-ref _ , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab {𝓁 = 𝓁} 𝓁≼𝓁′ ⊢v) (<:-Lab ≺:-¿ T₁<:T₂)
  with <:→no-blame {pc = pc} ⊢v T₁<:T₂
... | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab 𝓁 w , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab {𝓁 = 𝓁} 𝓁≼𝓁′ ⊢v) (<:-Lab (≺:-l {𝓁₂ = 𝓁₂} 𝓵′≼𝓁₂) T₁<:T₂)
  with 𝓁 ≼? 𝓁₂
... | no 𝓁⊀𝓁₂ = ⊥-elim (𝓁⊀𝓁₂ 𝓁≼𝓁₂)
  where
  𝓁≼𝓁₂ = ≼-trans 𝓁≼𝓁′ 𝓵′≼𝓁₂
... | yes _ with <:→no-blame {pc = pc} ⊢v T₁<:T₂
...   | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab 𝓁 w , refl ⟩
<:→no-blame {pc = pc} (⊢ᵥlab-dyn ⊢v) (<:-Lab ≺:-¿ T₁<:T₂) with <:→no-blame {pc = pc} ⊢v T₁<:T₂
... | ⟨ w , eq ⟩ rewrite eq = ⟨ V-lab _ w , refl ⟩
<:→no-blame (⊢ᵥclos _ _) (<:-⇒ _ _ _ _) = ⟨ V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _ , refl ⟩
<:→no-blame (⊢ᵥproxy _) (<:-⇒ _ _ _ _) = ⟨ V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _ , refl ⟩

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
𝒱-pres-pc≲ 0 _ _ _ _ _ ()
𝒱-pres-pc≲ {γ = γ} (suc k) 𝓁ᶜ₁≾𝓁₁ _ _ _ (⊢` {x = x} eq) eq₁
  with nth γ x
... | nothing = ⊥-elim (error≢result eq₁)
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
... | error _ | _ | _ | _ | _ = ⊥-elim (error≢result eq)
... | result ⟨ μ′ , v′ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ | WFresult freshμ′ | WTenv-result μ′⊢γ | [ eq₁ ]
  with castT μ′ 𝓁ᶜ′ T′ T v′ | ⊢castT {μ′} {𝓁ᶜ′} {T′} {T} ⊢μ′ ⊢v′ | castT-state-idem {μ′} {𝓁ᶜ′} {T′} {T} ⊢v′
...   | result ⟨ μ″ , v″ , 𝓁ᶜ″ ⟩ | ⊢ᵣresult ⊢μ″ ⊢v″ | ▹result μ′≡μ″ 𝓁ᶜ′≡𝓁ᶜ″ rewrite (sym μ′≡μ″) =
  let 𝓁ᶜ′≾𝓁₂ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let 𝓁ᶜ″≾𝓁₂ = subst (λ □ → l̂ □ ≾ 𝓁̂₂) 𝓁ᶜ′≡𝓁ᶜ″ 𝓁ᶜ′≾𝓁₂ in
    𝒱-pres-pc≲ k 𝓁ᶜ″≾𝓁₂ ⊢μ″ (⊢ₑ∷ ⊢v″ μ′⊢γ) freshμ′ ⊢N eq


𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {x = x} _ ⊢M ⊢N _) eq with nth γ x
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ ⊢μ₁ ⊢γ fresh (⊢if _ ⊢M ⊢N _) eq | just V-true
  with 𝒱 γ _ ⊢M μ₁ 𝓁ᶜ₁ k | 𝒱-safe {Γ} k 𝓁ᶜ₁ ⊢μ₁ fresh ⊢γ ⊢M | inspect (λ ⊢M → 𝒱 γ _ ⊢M μ₁ 𝓁ᶜ₁ k) ⊢M
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-true | error _ | _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq
  | just V-true | result ⟨ μ′ , vₘ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _
  with castL μ′ 𝓁ᶜ′ 𝓁̂₂ (𝓁̂₂ ⋎ 𝓁̂₂′) (𝓁̂≾𝓁̂⋎𝓁̂′ _ _) | castL-state-idem {μ′} {𝓁ᶜ′} {𝓁̂₂} {𝓁̂₂ ⋎ 𝓁̂₂′} (𝓁̂≾𝓁̂⋎𝓁̂′ _ _)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-true | result ⟨ μ′ , vₘ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _ | timeout | _ = ⊥-elim (timeout≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-true | result ⟨ μ′ , vₘ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _ | error _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if {T = T} {T′} {T″} _ ⊢M ⊢N _) eq
  | just V-true | result ⟨ μ′ , vₘ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | ▹result μ′≡μ″ _
  with castT μ″ 𝓁ᶜ″ T T″ vₘ | castT-state-idem {μ″} {𝓁ᶜ″} {T} {T″} μ″⊢vₘ
  where
  μ″⊢vₘ = subst (λ □ → □ ⊢ᵥ vₘ ⦂ _) μ′≡μ″ ⊢vₘ
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-true | result _ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | _ | timeout | _ = ⊥-elim (timeout≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-true | result _ | ⊢ᵣresult ⊢μ′ ⊢vₘ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | _ | error _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {T = T} {T′} {T″} {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq
  | just V-true | result _ | ⊢ᵣresult ⊢μ′ ⊢vₘ | [ eq₁ ] | result _ | ▹result _ 𝓁ᶜ′≡𝓁ᶜ″ | result _ | ▹result _ 𝓁ᶜ″≡𝓁ᶜ₂′ =
  let 𝓁ᶜ′≾𝓁₂ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢M eq₁ in
  let 𝓁ᶜ₂′≡𝓁ᶜ₂ = result≡→𝓁ᶜ≡ eq in
  let 𝓁ᶜ₂≾𝓁₂ = subst (λ □ → l̂ □ ≾ 𝓁̂₂) (trans 𝓁ᶜ′≡𝓁ᶜ″ (trans 𝓁ᶜ″≡𝓁ᶜ₂′ 𝓁ᶜ₂′≡𝓁ᶜ₂)) 𝓁ᶜ′≾𝓁₂ in
    𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ 𝓁ᶜ₂≾𝓁₂
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ ⊢μ₁ ⊢γ fresh (⊢if _ ⊢M ⊢N _) eq | just V-false
  with 𝒱 γ _ ⊢N μ₁ 𝓁ᶜ₁ k | 𝒱-safe {Γ} k 𝓁ᶜ₁ ⊢μ₁ fresh ⊢γ ⊢N | inspect (λ ⊢N → 𝒱 γ _ ⊢N μ₁ 𝓁ᶜ₁ k) ⊢N
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-false | error _ | _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq
  | just V-false | result ⟨ μ′ , vₙ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _
  with castL μ′ 𝓁ᶜ′ 𝓁̂₂′ (𝓁̂₂ ⋎ 𝓁̂₂′) (𝓁̂≾𝓁̂′⋎𝓁̂ _ _) | castL-state-idem {μ′} {𝓁ᶜ′} {𝓁̂₂′} {𝓁̂₂ ⋎ 𝓁̂₂′} (𝓁̂≾𝓁̂′⋎𝓁̂ _ _)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-false | result ⟨ μ′ , vₙ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _ | timeout | _ = ⊥-elim (timeout≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-false | result ⟨ μ′ , vₙ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _ | error _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if {T = T} {T′} {T″} _ ⊢M ⊢N _) eq
  | just V-false | result ⟨ μ′ , vₙ , 𝓁ᶜ′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | ▹result μ′≡μ″ _
  with castT μ″ 𝓁ᶜ″ T′ T″ vₙ | castT-state-idem {μ″} {𝓁ᶜ″} {T′} {T″} μ″⊢vₙ
  where
  μ″⊢vₙ = subst (λ □ → □ ⊢ᵥ vₙ ⦂ _) μ′≡μ″ ⊢vₙ
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-false | result _ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | _ | timeout | _ = ⊥-elim (timeout≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) _ _ _ _ (⊢if _ ⊢M ⊢N _) eq
  | just V-false | result _ | ⊢ᵣresult ⊢μ′ ⊢vₙ | _ | result ⟨ μ″ , _ , 𝓁ᶜ″ ⟩ | _ | error _ | _ = ⊥-elim (error≢result eq)
𝒱-pres-pc≲ {Γ} {γ} {μ₁} {μ₂} {𝓁ᶜ₁} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh (⊢if {T = T} {T′} {T″} {𝓁̂₂ = 𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) eq
  | just V-false | result _ | ⊢ᵣresult ⊢μ′ ⊢vₙ | [ eq₁ ] | result _ | ▹result _ 𝓁ᶜ′≡𝓁ᶜ″ | result _ | ▹result _ 𝓁ᶜ″≡𝓁ᶜ₂′ =
  let 𝓁ᶜ′≾𝓁₂′ = 𝒱-pres-pc≲ k 𝓁ᶜ₁≾𝓁₁ ⊢μ₁ ⊢γ fresh ⊢N eq₁ in
  let 𝓁ᶜ₂′≡𝓁ᶜ₂ = result≡→𝓁ᶜ≡ eq in
  let 𝓁ᶜ₂≾𝓁₂′ = subst (λ □ → l̂ □ ≾ 𝓁̂₂′) (trans 𝓁ᶜ′≡𝓁ᶜ″ (trans 𝓁ᶜ″≡𝓁ᶜ₂′ 𝓁ᶜ₂′≡𝓁ᶜ₂)) 𝓁ᶜ′≾𝓁₂′ in
    subst (λ □ → l̂ _ ≾ □) (⋎-comm 𝓁̂₂′ 𝓁̂₂) (𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ 𝓁ᶜ₂≾𝓁₂′)


-- 𝒱-pres-pc≲ {γ = γ} {μ₁ = μ₁} {𝓁ᶜ₁ = 𝓁ᶜ₁} {𝓁ᶜ₂} (suc k) 𝓁ᶜ₁≾𝓁₁ ⊢γ (⊢get {x = x} _) eq with nth γ x | inspect (λ □ → nth □ x) γ
-- ... | nothing | _ = ⊥-elim (error≢result eq)
-- ... | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) | [ eq₁ ] with lookup μ₁ ⟨ n , 𝓁₁ , 𝓁₂ ⟩
-- ...   | just ⟨ T′ , v ⟩ = {!!}
-- ...   | nothing = ⊥-elim (error≢result eq)

-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢set x x₁ x₂ x₃) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢new x x₁) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢new-dyn x x₁) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢eq-ref x x₁ x₂ x₃) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢ƛ tM) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢· x x₁ x₂ x₃) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢ref-label x) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢lab-label x) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ ⊢pc-label eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ ⊢label eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢≼ x x₁) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢⊔ x x₁) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢⊓ x x₁) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢unlabel x) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢to-label tM x) eq = {!!}
-- 𝒱-pres-pc≲ 𝓁ᶜ≾𝓁₁ (⊢to-label-dyn x tM) eq = {!!}
