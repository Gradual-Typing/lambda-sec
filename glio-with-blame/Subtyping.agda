open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties using (m≤n⇒m≤n⊔o)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import StaticsGLIOb
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)



infixl 9 _≺:_

data _≺:_ : ℒ̂ → ℒ̂ → Set where

  ≺:-¿ : ∀ {𝓁̂} → 𝓁̂ ≺: ¿

  ≺-l : ∀ {𝓁₁ 𝓁₂}
    → 𝓁₁ ≼ 𝓁₂
    → (l̂ 𝓁₁) ≺: (l̂ 𝓁₂)

𝓁⋎¿≡¿ : ∀ 𝓁̂ → 𝓁̂ ⋎ ¿ ≡ ¿
𝓁⋎¿≡¿ ¿ = refl
𝓁⋎¿≡¿ (l̂ _) = refl

𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ : ∀ {𝓁 𝓁₁ 𝓁₂}
  → 𝓁 ≼ 𝓁₁
  → 𝓁 ≼ 𝓁₁ ⊔ 𝓁₂
𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ {l n} {l n₁} {l n₂} (≼-l n≤n₁) = ≼-l (m≤n⇒m≤n⊔o n₂ n≤n₁)

𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ : ∀ {𝓁 𝓁̂₁ 𝓁̂₂}
  → (l̂ 𝓁) ≾ 𝓁̂₁
  → (l̂ 𝓁) ≺: 𝓁̂₁ ⋎ 𝓁̂₂
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {𝓁̂₁} {¿} 𝓁≾𝓁₁ rewrite 𝓁⋎¿≡¿ 𝓁̂₁ = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {¿} {l̂ _} leq = ≺:-¿
𝓁≾𝓁₁→𝓁≺:𝓁₁⋎𝓁₂ {𝓁} {l̂ 𝓁₁} {l̂ 𝓁₂} (≾-l 𝓁≼𝓁₁) = ≺-l (𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ 𝓁≼𝓁₁)
