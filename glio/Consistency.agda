module Consistency where

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import StaticsGLIO
open import Lemmas using (≼-refl; ≼-antisym)
open import Iff using (_⇔_)



-- Consistency for labels
infixl 9 _~_

data _~_ : ℒ̂ → ℒ̂ → Set where

  ~-¿-r : ∀ {𝓁̂} → 𝓁̂ ~ ¿

  ~-¿-l : ∀ {𝓁̂} → ¿ ~ 𝓁̂

  ~-l : ∀ {𝓁} → (l̂ 𝓁) ~ (l̂ 𝓁)

-- Consistency for types
infixl 9 _∼_

data _∼_ : 𝕋 → 𝕋 → Set where

  ∼-⊤ : `⊤ ∼ `⊤

  ∼-𝔹 : `𝔹 ∼ `𝔹

  ∼-ℒ : `ℒ ∼ `ℒ

  ∼-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₂
    → T₁ ∼ T₂
      ----------------------
    → Ref 𝓁̂₁ T₁ ∼ Ref 𝓁̂₂ T₂

  ∼-Lab : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₂
    → T₁ ∼ T₂
      ----------------------
    → Lab 𝓁̂₁ T₁ ∼ Lab 𝓁̂₂ T₂

  ∼-⇒ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S₁ S₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₁′
    → 𝓁̂₂ ~ 𝓁̂₂′
    → S₁ ∼ T₁
    → S₂ ∼ T₂
      ---------------------------------------------------
    → (S₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S₂) ∼ (T₁ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂)

𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 : ∀ 𝓁̂ 𝓁̂′ → (𝓁̂ ~ 𝓁̂′) ⇔ (𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂)
𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 𝓁̂ 𝓁̂′ = record { to = to ; from = from }
  where
  to : 𝓁̂ ~ 𝓁̂′ → 𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂
  to ~-¿-r = ⟨ ≾-¿-r , ≾-¿-l ⟩
  to ~-¿-l = ⟨ ≾-¿-l , ≾-¿-r ⟩
  to ~-l = ⟨ ≾-l (≼-refl _) , ≾-l (≼-refl _) ⟩

  from : 𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂ → 𝓁̂ ~ 𝓁̂′
  from ⟨ ≾-¿-r , _ ⟩ = ~-¿-r
  from ⟨ ≾-¿-l , _ ⟩ = ~-¿-l
  from ⟨ ≾-l 𝓁≼𝓁′ , ≾-l 𝓁′≼𝓁 ⟩ rewrite ≼-antisym 𝓁≼𝓁′ 𝓁′≼𝓁 = ~-l
