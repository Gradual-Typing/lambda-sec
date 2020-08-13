module Subtyping where

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
