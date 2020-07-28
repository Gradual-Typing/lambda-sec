open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties using (m≤m⊔n; m≤n⇒m≤n⊔o)
open import Data.Empty using (⊥; ⊥-elim)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import StaticsGLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Lemmas
open import Interp



infixl 9 _≺:_

data _≺:_ : ℒ̂ → ℒ̂ → Set where

  ≺:-¿ : ∀ {𝓁̂}
       ------
    → 𝓁̂ ≺: ¿

  ≺-l : ∀ {𝓁₁ 𝓁₂}
    → 𝓁₁ ≼ 𝓁₂
      -----------------
    → (l̂ 𝓁₁) ≺: (l̂ 𝓁₂)



𝓁⋎¿≡¿ : ∀ 𝓁̂ → 𝓁̂ ⋎ ¿ ≡ ¿
𝓁⋎¿≡¿ ¿ = refl
𝓁⋎¿≡¿ (l̂ _) = refl

𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ : ∀ {𝓁 𝓁₁}
  → (𝓁₂ : ℒ)
  → 𝓁 ≼ 𝓁₁
  → 𝓁 ≼ 𝓁₁ ⊔ 𝓁₂
𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ {l n} {l n₁} (l n₂) (≼-l n≤n₁) = ≼-l (m≤n⇒m≤n⊔o n₂ n≤n₁)

𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ : ∀ {𝓁 𝓁̂₁}
  → (𝓁̂₂ : ℒ̂)
  → (l̂ 𝓁) ≾ 𝓁̂₁
  → (l̂ 𝓁) ≺: 𝓁̂₁ ⋎ 𝓁̂₂
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {𝓁̂₁} ¿ 𝓁≾𝓁₁ rewrite 𝓁⋎¿≡¿ 𝓁̂₁ = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {¿} (l̂ _) _ = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {l̂ 𝓁₁} (l̂ 𝓁₂) (≾-l 𝓁≼𝓁₁) = ≺-l (𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ 𝓁₂ 𝓁≼𝓁₁)

𝓁≺:𝓁⋎𝓁′ : ∀ 𝓁̂ 𝓁̂′ → 𝓁̂ ≺: 𝓁̂ ⋎ 𝓁̂′
𝓁≺:𝓁⋎𝓁′ 𝓁̂ ¿ rewrite 𝓁⋎¿≡¿ 𝓁̂ = ≺:-¿
𝓁≺:𝓁⋎𝓁′ ¿ (l̂ 𝓁′) = ≺:-¿
𝓁≺:𝓁⋎𝓁′ (l̂ 𝓁) (l̂ 𝓁′) = ≺-l (𝓁≼𝓁⊔𝓁′ 𝓁 𝓁′)

-- ≺: is smaller than ≾
𝓁≺:𝓁′→𝓁≾𝓁′ : ∀ {𝓁 𝓁′}
  → 𝓁 ≺: 𝓁′
  → 𝓁 ≾ 𝓁′
𝓁≺:𝓁′→𝓁≾𝓁′ ≺:-¿ = ≾-¿-r
𝓁≺:𝓁′→𝓁≾𝓁′ (≺-l 𝓁₁≼𝓁₂) = ≾-l 𝓁₁≼𝓁₂

-- Consistent subtyping ≾ is not transitive; alternatively, we have:
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₃}
  → 𝓁̂₁ ≾ 𝓁̂₂
  → 𝓁̂₂ ≺: 𝓁̂₃
  → 𝓁̂₁ ≾ 𝓁̂₃
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-r ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-l ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ (≾-l _) ≺:-¿ = ≾-¿-r
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ ≾-¿-l (≺-l _) = ≾-¿-l
𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ {l̂ 𝓁₁} {l̂ 𝓁₂} {l̂ 𝓁₃} (≾-l 𝓁₁≼𝓁₂) (≺-l 𝓁₂≼𝓁₃) = ≾-l (≼-trans 𝓁₁≼𝓁₂ 𝓁₂≼𝓁₃)

-- CastL 𝓁̂₁ ⇛ 𝓁̂₂ never fails if 𝓁̂₁ ≺: 𝓁̂₂
≺:→no-blame : ∀ {μ pc 𝓁̂₁ 𝓁̂₂}
  → (l̂ pc) ≾ 𝓁̂₁
  → (𝓁̂₁≺:𝓁̂₂ : 𝓁̂₁ ≺: 𝓁̂₂)
  → castL μ pc 𝓁̂₁ 𝓁̂₂ (𝓁≺:𝓁′→𝓁≾𝓁′ 𝓁̂₁≺:𝓁̂₂) ≢ error castError
≺:→no-blame {pc = pc} {𝓁̂₁} {𝓁̂₂} pc≾𝓁₁ 𝓁₁≺:𝓁₂
  with (l̂ pc) ≾? 𝓁̂₂
... | yes pc≾𝓁₂ = λ ()
... | no pc⊀𝓁₂ = ⊥-elim (pc⊀𝓁₂ pc≾𝓁₂)
  where
  pc≾𝓁₂ = 𝓁₁≾𝓁₂→𝓁₂≺:𝓁₃→𝓁₁≾𝓁₃ pc≾𝓁₁ 𝓁₁≺:𝓁₂



infixl 9 _≃_

data _≃_ : ℒ̂ → ℒ̂ → Set where

  ≃-¿ : ∀ {𝓁̂}
      ------
    → 𝓁̂ ≃ ¿

  ≃-l : ∀ {𝓁}
      ---------------
    → (l̂ 𝓁) ≃ (l̂ 𝓁)

infixl 9 _<:_

data _<:_ : 𝕋 → 𝕋 → Set where

  <:-⊤ : `⊤ <: `⊤

  <:-𝔹 : `𝔹 <: `𝔹

  <:-ℒ : `ℒ <: `ℒ

  <:-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ≃ 𝓁̂₂
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
