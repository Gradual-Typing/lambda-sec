module Lemmas where

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _>_; z≤n; s≤s; _≤?_) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; m≤m⊔n; m≤n⇒m≤n⊔o; m≤n⇒n⊔m≡n; m≤n⇒m⊔n≡n; ≰⇒>)
  renaming (⊔-comm to ⊔ₙ-comm)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)

open import StaticsGLIO



≼-refl : ∀ 𝓁 → 𝓁 ≼ 𝓁
≼-refl (l n) = ≼-l {n} {n} ≤-refl

≾-refl : ∀ 𝓁̂ → 𝓁̂ ≾ 𝓁̂
≾-refl ¿     = ≾-¿-r
≾-refl (l̂ 𝓁) = ≾-l (≼-refl _)

⊔-comm : ∀ 𝓁₁ 𝓁₂ → 𝓁₁ ⊔ 𝓁₂ ≡ 𝓁₂ ⊔ 𝓁₁
⊔-comm (l n₁) (l n₂) = cong l (⊔ₙ-comm n₁ n₂)

⋎-comm : ∀ 𝓁̂₁ 𝓁̂₂ → 𝓁̂₁ ⋎ 𝓁̂₂ ≡ 𝓁̂₂ ⋎ 𝓁̂₁
⋎-comm ¿      ¿      = refl
⋎-comm ¿      (l̂ 𝓁)  = refl
⋎-comm (l̂ 𝓁)  ¿      = refl
⋎-comm (l̂ 𝓁₁) (l̂ 𝓁₂) = cong l̂ (⊔-comm _ _)

¿⋎𝓁̂≡¿ : ∀ 𝓁̂ → ¿ ⋎ 𝓁̂ ≡ ¿
¿⋎𝓁̂≡¿ ¿ = refl
¿⋎𝓁̂≡¿ (l̂ _) = refl

𝓁̂⋎¿≡¿ : ∀ 𝓁̂ → 𝓁̂ ⋎ ¿ ≡ ¿
𝓁̂⋎¿≡¿ ¿ = refl
𝓁̂⋎¿≡¿ (l̂ _) = refl

𝓁≼𝓁⊔𝓁′ : ∀ 𝓁 𝓁′ → 𝓁 ≼ (𝓁 ⊔ 𝓁′)
𝓁≼𝓁⊔𝓁′ (l n) (l n′) = ≼-l (m≤m⊔n n n′)

𝓁̂≾𝓁̂⋎𝓁̂′ : ∀ 𝓁̂ 𝓁̂′ → 𝓁̂ ≾ (𝓁̂ ⋎ 𝓁̂′)
𝓁̂≾𝓁̂⋎𝓁̂′ ¿      ¿      = ≾-¿-r
𝓁̂≾𝓁̂⋎𝓁̂′ ¿      (l̂ 𝓁)  = ≾-¿-r
𝓁̂≾𝓁̂⋎𝓁̂′ (l̂ 𝓁)  ¿      = ≾-¿-r
𝓁̂≾𝓁̂⋎𝓁̂′ (l̂ 𝓁₁) (l̂ 𝓁₂) = ≾-l (𝓁≼𝓁⊔𝓁′ _ _)

𝓁̂≾𝓁̂′⋎𝓁̂ : ∀ 𝓁̂ 𝓁̂′ → 𝓁̂ ≾ (𝓁̂′ ⋎ 𝓁̂)
𝓁̂≾𝓁̂′⋎𝓁̂ 𝓁̂ 𝓁̂′ rewrite ⋎-comm 𝓁̂′ 𝓁̂ = 𝓁̂≾𝓁̂⋎𝓁̂′ _ _

𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ : ∀ {𝓁 𝓁₁}
  → (𝓁₂ : ℒ)
  → 𝓁 ≼ 𝓁₁
    ------------
  → 𝓁 ≼ 𝓁₁ ⊔ 𝓁₂
𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ {l n} {l n₁} (l n₂) (≼-l n≤n₁) = ≼-l (m≤n⇒m≤n⊔o n₂ n≤n₁)

𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₃}
  → 𝓁̂₁ ≾ 𝓁̂₂
  → 𝓁̂₁ ≾ 𝓁̂₂ ⋎ 𝓁̂₃
𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ {𝓁̂₃ = 𝓁̂₃} ≾-¿-r rewrite ¿⋎𝓁̂≡¿ 𝓁̂₃ = ≾-¿-r
𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ ≾-¿-l = ≾-¿-l
𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ {𝓁̂₃ = ¿} (≾-l 𝓁₁≼𝓁₂) = ≾-¿-r
𝓁≾𝓁₁→𝓁≾𝓁₁⋎𝓁₂ {𝓁̂₃ = l̂ 𝓁₃} (≾-l 𝓁₁≼𝓁₂) = ≾-l (𝓁≼𝓁₁→𝓁≼𝓁₁⊔𝓁₂ _ 𝓁₁≼𝓁₂)

nothing≢just : ∀ {X : Set} {x : X} → nothing ≢ just x
nothing≢just = λ ()

just≢nothing : ∀ {X : Set} {x : X} → just x ≢ nothing
just≢nothing = λ ()

just-≡-inv : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-≡-inv refl = refl

×-≡-inv : ∀ {X Y : Set} {x₁ x₂ : X} {y₁ y₂ : Y} → ⟨ x₁ , y₁ ⟩ ≡ ⟨ x₂ , y₂ ⟩ → (x₁ ≡ x₂) × (y₁ ≡ y₂)
×-≡-inv refl = ⟨ refl , refl ⟩

≼-trans : ∀ {𝓁₁ 𝓁₂ 𝓁₃}
  → 𝓁₁ ≼ 𝓁₂
  → 𝓁₂ ≼ 𝓁₃
    ---------
  → 𝓁₁ ≼ 𝓁₃
≼-trans {l n₁} {l n₂} {l n₃} (≼-l n₁≤n₂) (≼-l n₂≤n₃) = ≼-l {n₁} {n₃} (≤-trans n₁≤n₂ n₂≤n₃)

≼-antisym : ∀ {𝓁₁ 𝓁₂}
  → 𝓁₁ ≼ 𝓁₂
  → 𝓁₂ ≼ 𝓁₁
    --------
  → 𝓁₁ ≡ 𝓁₂
≼-antisym {l n₁} {l n₂} (≼-l n₁≤n₂) (≼-l n₂≤n₁) = cong l (≤-antisym n₁≤n₂ n₂≤n₁)

m≤n⇒m≤sn : ∀ {m n} → m ≤ n → m ≤ suc n
m≤n⇒m≤sn z≤n = z≤n
m≤n⇒m≤sn (s≤s leq) = s≤s (m≤n⇒m≤sn leq)

m>n⇒n≤m : ∀ {m n} → m > n → n ≤ m
m>n⇒n≤m {suc m} (s≤s m>n) = m≤n⇒m≤sn m>n

m≤n⇒m⊔o≤n⊔o : ∀ {m n} o
  → m ≤ n
  → m ⊔ₙ o ≤ n ⊔ₙ o
m≤n⇒m⊔o≤n⊔o {m} {n} o m≤n with o ≤? m
... | yes o≤m rewrite (m≤n⇒n⊔m≡n o≤m) | (m≤n⇒n⊔m≡n (≤-trans o≤m m≤n)) = m≤n
... | no  o≰m with o ≤? n
...   | yes o≤n rewrite (m≤n⇒m⊔n≡n (m>n⇒n≤m (≰⇒> o≰m))) | (m≤n⇒n⊔m≡n o≤n) = o≤n
...   | no  o≰n rewrite (m≤n⇒m⊔n≡n (m>n⇒n≤m (≰⇒> o≰m))) | (m≤n⇒m⊔n≡n (m>n⇒n≤m (≰⇒> o≰n))) = ≤-refl

𝓁₁≼𝓁₂→𝓁₁⊔𝓁≼𝓁₂⊔𝓁 : ∀ {𝓁₁ 𝓁₂}
  → (𝓁 : ℒ)
  → 𝓁₁ ≼ 𝓁₂
  → 𝓁₁ ⊔ 𝓁 ≼ 𝓁₂ ⊔ 𝓁
𝓁₁≼𝓁₂→𝓁₁⊔𝓁≼𝓁₂⊔𝓁 (l n) (≼-l n₁≤n₂) = ≼-l (m≤n⇒m⊔o≤n⊔o n n₁≤n₂)

𝓁₁≾𝓁̂→𝓁₁⊔𝓁₂≾𝓁̂⋎𝓁₂ : ∀ {𝓁̂ 𝓁₁ 𝓁₂}
  → (l̂ 𝓁₁) ≾ 𝓁̂
  → l̂ (𝓁₁ ⊔ 𝓁₂) ≾ 𝓁̂ ⋎ (l̂ 𝓁₂)
𝓁₁≾𝓁̂→𝓁₁⊔𝓁₂≾𝓁̂⋎𝓁₂ ≾-¿-r = ≾-¿-r
𝓁₁≾𝓁̂→𝓁₁⊔𝓁₂≾𝓁̂⋎𝓁₂ {l̂ 𝓁} {𝓁₁} {𝓁₂} (≾-l 𝓁₁≼𝓁) = ≾-l (𝓁₁≼𝓁₂→𝓁₁⊔𝓁≼𝓁₂⊔𝓁 𝓁₂ 𝓁₁≼𝓁)
