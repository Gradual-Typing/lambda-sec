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
open import Lemmas
open import Interp
open import WellTypedness using (_⊢ᵥ_⦂_)
open import Store



infixl 9 _≺:_

data _≺:_ : ℒ̂ → ℒ̂ → Set where

  ≺:-¿ : ∀ {ℓ̂}
       ------
    → ℓ̂ ≺: ¿

  ≺:-l : ∀ {ℓ₁ ℓ₂}
    → ℓ₁ ≼ ℓ₂
      -----------------
    → (l̂ ℓ₁) ≺: (l̂ ℓ₂)



ℓ≾ℓ₁→ℓ≺:ℓ₁⋎ℓ₂ : ∀ {ℓ ℓ̂₁}
  → (ℓ̂₂ : ℒ̂)
  → (l̂ ℓ) ≾ ℓ̂₁
    -----------------
  → (l̂ ℓ) ≺: ℓ̂₁ ⋎ ℓ̂₂
ℓ≾ℓ₁→ℓ≺:ℓ₁⋎ℓ₂ {ℓ} {ℓ̂₁} ¿ ℓ≾ℓ₁ rewrite ℓ̂⋎¿≡¿ ℓ̂₁ = ≺:-¿
ℓ≾ℓ₁→ℓ≺:ℓ₁⋎ℓ₂ {ℓ} {¿} (l̂ _) _ = ≺:-¿
ℓ≾ℓ₁→ℓ≺:ℓ₁⋎ℓ₂ {ℓ} {l̂ ℓ₁} (l̂ ℓ₂) (≾-l ℓ≼ℓ₁) = ≺:-l (ℓ≼ℓ₁→ℓ≼ℓ₁⊔ℓ₂ ℓ₂ ℓ≼ℓ₁)

ℓ≺:ℓ⋎ℓ′ : ∀ ℓ̂ ℓ̂′ → ℓ̂ ≺: ℓ̂ ⋎ ℓ̂′
ℓ≺:ℓ⋎ℓ′ ℓ̂ ¿ rewrite ℓ̂⋎¿≡¿ ℓ̂ = ≺:-¿
ℓ≺:ℓ⋎ℓ′ ¿ (l̂ ℓ′) = ≺:-¿
ℓ≺:ℓ⋎ℓ′ (l̂ ℓ) (l̂ ℓ′) = ≺:-l (ℓ≼ℓ⊔ℓ′ ℓ ℓ′)

-- ≺: is smaller than ≾
≺:→≾ : ∀ {ℓ ℓ′}
  → ℓ ≺: ℓ′
    --------
  → ℓ ≾ ℓ′
≺:→≾ ≺:-¿ = ≾-¿-r
≺:→≾ (≺:-l ℓ₁≼ℓ₂) = ≾-l ℓ₁≼ℓ₂

-- Consistent subtyping ≾ is not transitive; alternatively, we have:
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ : ∀ {ℓ̂₁ ℓ̂₂ ℓ̂₃}
  → ℓ̂₁ ≾ ℓ̂₂
  → ℓ̂₂ ≺: ℓ̂₃
    ---------
  → ℓ̂₁ ≾ ℓ̂₃
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ ≾-¿-r ≺:-¿ = ≾-¿-r
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ ≾-¿-l ≺:-¿ = ≾-¿-r
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ (≾-l _) ≺:-¿ = ≾-¿-r
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ ≾-¿-l (≺:-l _) = ≾-¿-l
ℓ₁≾ℓ₂→ℓ₂≺:ℓ₃→ℓ₁≾ℓ₃ {l̂ ℓ₁} {l̂ ℓ₂} {l̂ ℓ₃} (≾-l ℓ₁≼ℓ₂) (≺:-l ℓ₂≼ℓ₃) = ≾-l (≼-trans ℓ₁≼ℓ₂ ℓ₂≼ℓ₃)



infixl 9 _≂_

data _≂_ : ℒ̂ → ℒ̂ → Set where

  ≂-¿ : ∀ {ℓ̂}
      ------
    → ℓ̂ ≂ ¿

  ≂-l : ∀ {ℓ}
      ---------------
    → (l̂ ℓ) ≂ (l̂ ℓ)

infixl 9 _<:_

data _<:_ : 𝕋 → 𝕋 → Set where

  <:-⊤ : `⊤ <: `⊤

  <:-𝔹 : `𝔹 <: `𝔹

  <:-ℒ : `ℒ <: `ℒ

  <:-Ref : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ≂ ℓ̂₂
    → T₁ ≲ T₂ → T₂ ≲ T₁
      -----------------------
    → Ref ℓ̂₁ T₁ <: Ref ℓ̂₂ T₂

  <:-Lab : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ≺: ℓ̂₂
    → T₁ <: T₂
      -----------------------
    → Lab ℓ̂₁ T₁ <: Lab ℓ̂₂ T₂

  <:-⇒ : ∀ {ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S₁ S₂ T₁ T₂}
    → ℓ̂₁′ ≺: ℓ̂₁
    → ℓ̂₂ ≺: ℓ̂₂′
    → T₁ <: S₁
    → S₂ <: T₂
      ---------------------------------------------------
    → (S₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S₂) <: (T₁ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂)



≂→≾ : ∀ {ℓ̂₁ ℓ̂₂}
  → ℓ̂₁ ≂ ℓ̂₂
    ------------------
  → ℓ̂₁ ≾ ℓ̂₂ × ℓ̂₂ ≾ ℓ̂₁
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
<:→≲ (<:-Ref ℓ₁≂ℓ₂ T₁≲T₂ T₂≲T₁) =
  let ⟨ ℓ₁≾ℓ₂ , ℓ₂≾ℓ₁ ⟩ = ≂→≾ ℓ₁≂ℓ₂ in
    ≲-Ref ℓ₁≾ℓ₂ ℓ₂≾ℓ₁ T₁≲T₂ T₂≲T₁
<:→≲ (<:-Lab ℓ₁≺:ℓ₂ T₁<:T₂) = ≲-Lab (≺:→≾ ℓ₁≺:ℓ₂) (<:→≲ T₁<:T₂)
<:→≲ (<:-⇒ ℓ₁′≺:ℓ₁ ℓ₂≺:ℓ₂′ T₁<:S₁ S₂<:T₂) = ≲-⇒ (≺:→≾ ℓ₁′≺:ℓ₁) (≺:→≾ ℓ₂≺:ℓ₂′) (<:→≲ T₁<:S₁) (<:→≲ S₂<:T₂)
