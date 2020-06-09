open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties using (≤-refl; ≤-trans) renaming (⊔-comm to ⊔ₙ-comm)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)

open import StaticsLIO



⊑-refl : ∀ {𝓁} → 𝓁 ⊑ 𝓁
⊑-refl {l n} = ⊑-l {n} {n} ≤-refl

⊑̂-refl : ∀ {𝓁̂} → 𝓁̂ ⊑̂ 𝓁̂
⊑̂-refl {¿} = ⊑̂-¿-r
⊑̂-refl {l̂ 𝓁} = ⊑̂-l ⊑-refl

⊔-comm : ∀ {𝓁₁ 𝓁₂} → 𝓁₁ ⊔ 𝓁₂ ≡ 𝓁₂ ⊔ 𝓁₁
⊔-comm {l n₁} {l n₂} = cong l (⊔ₙ-comm n₁ n₂)

⊔̂-comm : ∀ {𝓁̂₁ 𝓁̂₂} → 𝓁̂₁ ⊔̂ 𝓁̂₂ ≡ 𝓁̂₂ ⊔̂ 𝓁̂₁
⊔̂-comm {¿} {¿} = refl
⊔̂-comm {¿} {l̂ 𝓁} = refl
⊔̂-comm {l̂ 𝓁} {¿} = refl
⊔̂-comm {l̂ 𝓁₁} {l̂ 𝓁₂} = cong l̂ ⊔-comm

postulate
  𝓁̂⊑̂𝓁̂⊔̂𝓁̂′ : ∀ {𝓁̂ 𝓁̂′} → 𝓁̂ ⊑̂ (𝓁̂ ⊔̂ 𝓁̂′)

𝓁̂⊑̂𝓁̂′⊔̂𝓁̂ : ∀ {𝓁̂ 𝓁̂′} → 𝓁̂ ⊑̂ (𝓁̂′ ⊔̂ 𝓁̂)
𝓁̂⊑̂𝓁̂′⊔̂𝓁̂ {𝓁̂} {𝓁̂′} rewrite ⊔̂-comm {𝓁̂′} {𝓁̂} = 𝓁̂⊑̂𝓁̂⊔̂𝓁̂′
