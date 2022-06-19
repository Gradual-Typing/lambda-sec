module Lemmas where

open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Nat using (ℕ; zero; suc; _≤_; _>_; z≤n; s≤s; _≤?_) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties
  using (≤-refl; ≤-trans; ≤-antisym; m≤m⊔n; m≤n⇒m≤n⊔o; m≤n⇒n⊔m≡n; m≤n⇒m⊔n≡n; ≰⇒>)
  renaming (⊔-comm to ⊔ₙ-comm; ⊔-monoˡ-≤ to ⊔ₙ-monoˡ-≤; ⊔-mono-≤ to ⊔ₙ-mono-≤)
open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂)

open import StaticsGLIO



≼-refl : ∀ ℓ → ℓ ≼ ℓ
≼-refl (l n) = ≼-l {n} {n} ≤-refl

≾-refl : ∀ ℓ̂ → ℓ̂ ≾ ℓ̂
≾-refl ¿     = ≾-¿-r
≾-refl (l̂ ℓ) = ≾-l (≼-refl _)

⊔-comm : ∀ ℓ₁ ℓ₂ → ℓ₁ ⊔ ℓ₂ ≡ ℓ₂ ⊔ ℓ₁
⊔-comm (l n₁) (l n₂) = cong l (⊔ₙ-comm n₁ n₂)

⋎-comm : ∀ ℓ̂₁ ℓ̂₂ → ℓ̂₁ ⋎ ℓ̂₂ ≡ ℓ̂₂ ⋎ ℓ̂₁
⋎-comm ¿      ¿      = refl
⋎-comm ¿      (l̂ ℓ)  = refl
⋎-comm (l̂ ℓ)  ¿      = refl
⋎-comm (l̂ ℓ₁) (l̂ ℓ₂) = cong l̂ (⊔-comm _ _)

¿⋎ℓ̂≡¿ : ∀ ℓ̂ → ¿ ⋎ ℓ̂ ≡ ¿
¿⋎ℓ̂≡¿ ¿ = refl
¿⋎ℓ̂≡¿ (l̂ _) = refl

ℓ̂⋎¿≡¿ : ∀ ℓ̂ → ℓ̂ ⋎ ¿ ≡ ¿
ℓ̂⋎¿≡¿ ¿ = refl
ℓ̂⋎¿≡¿ (l̂ _) = refl

ℓ≼ℓ⊔ℓ′ : ∀ ℓ ℓ′ → ℓ ≼ (ℓ ⊔ ℓ′)
ℓ≼ℓ⊔ℓ′ (l n) (l n′) = ≼-l (m≤m⊔n n n′)

ℓ̂≾ℓ̂⋎ℓ̂′ : ∀ ℓ̂ ℓ̂′ → ℓ̂ ≾ (ℓ̂ ⋎ ℓ̂′)
ℓ̂≾ℓ̂⋎ℓ̂′ ¿      ¿      = ≾-¿-r
ℓ̂≾ℓ̂⋎ℓ̂′ ¿      (l̂ ℓ)  = ≾-¿-r
ℓ̂≾ℓ̂⋎ℓ̂′ (l̂ ℓ)  ¿      = ≾-¿-r
ℓ̂≾ℓ̂⋎ℓ̂′ (l̂ ℓ₁) (l̂ ℓ₂) = ≾-l (ℓ≼ℓ⊔ℓ′ _ _)

ℓ̂≾ℓ̂′⋎ℓ̂ : ∀ ℓ̂ ℓ̂′ → ℓ̂ ≾ (ℓ̂′ ⋎ ℓ̂)
ℓ̂≾ℓ̂′⋎ℓ̂ ℓ̂ ℓ̂′ rewrite ⋎-comm ℓ̂′ ℓ̂ = ℓ̂≾ℓ̂⋎ℓ̂′ _ _

ℓ≼ℓ₁→ℓ≼ℓ₁⊔ℓ₂ : ∀ {ℓ ℓ₁}
  → (ℓ₂ : ℒ)
  → ℓ ≼ ℓ₁
    ------------
  → ℓ ≼ ℓ₁ ⊔ ℓ₂
ℓ≼ℓ₁→ℓ≼ℓ₁⊔ℓ₂ {l n} {l n₁} (l n₂) (≼-l n≤n₁) = ≼-l (m≤n⇒m≤n⊔o n₂ n≤n₁)

ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ : ∀ {ℓ̂₁ ℓ̂₂ ℓ̂₃}
  → ℓ̂₁ ≾ ℓ̂₂
    -------------
  → ℓ̂₁ ≾ ℓ̂₂ ⋎ ℓ̂₃
ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ {ℓ̂₃ = ℓ̂₃} ≾-¿-r rewrite ¿⋎ℓ̂≡¿ ℓ̂₃ = ≾-¿-r
ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ ≾-¿-l = ≾-¿-l
ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ {ℓ̂₃ = ¿} (≾-l ℓ₁≼ℓ₂) = ≾-¿-r
ℓ≾ℓ₁→ℓ≾ℓ₁⋎ℓ₂ {ℓ̂₃ = l̂ ℓ₃} (≾-l ℓ₁≼ℓ₂) = ≾-l (ℓ≼ℓ₁→ℓ≼ℓ₁⊔ℓ₂ _ ℓ₁≼ℓ₂)

nothing≢just : ∀ {X : Set} {x : X} → nothing ≢ just x
nothing≢just = λ ()

just≢nothing : ∀ {X : Set} {x : X} → just x ≢ nothing
just≢nothing = λ ()

just-≡-inv : ∀ {X : Set} {x y : X} → just x ≡ just y → x ≡ y
just-≡-inv refl = refl

×-≡-inv : ∀ {X Y : Set} {x₁ x₂ : X} {y₁ y₂ : Y} → ⟨ x₁ , y₁ ⟩ ≡ ⟨ x₂ , y₂ ⟩ → (x₁ ≡ x₂) × (y₁ ≡ y₂)
×-≡-inv refl = ⟨ refl , refl ⟩

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → ℓ₁ ≼ ℓ₂
  → ℓ₂ ≼ ℓ₃
    ---------
  → ℓ₁ ≼ ℓ₃
≼-trans {l n₁} {l n₂} {l n₃} (≼-l n₁≤n₂) (≼-l n₂≤n₃) = ≼-l {n₁} {n₃} (≤-trans n₁≤n₂ n₂≤n₃)

≼-antisym : ∀ {ℓ₁ ℓ₂}
  → ℓ₁ ≼ ℓ₂
  → ℓ₂ ≼ ℓ₁
    --------
  → ℓ₁ ≡ ℓ₂
≼-antisym {l n₁} {l n₂} (≼-l n₁≤n₂) (≼-l n₂≤n₁) = cong l (≤-antisym n₁≤n₂ n₂≤n₁)

⊔-mono-≼ : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
  → ℓ₁ ≼ ℓ₂
  → ℓ₃ ≼ ℓ₄
    ------------------
  → ℓ₁ ⊔ ℓ₃ ≼ ℓ₂ ⊔ ℓ₄
⊔-mono-≼ (≼-l n₁≤n₂) (≼-l n₃≤n₄) = ≼-l (⊔ₙ-mono-≤ n₁≤n₂ n₃≤n₄)

m≤n⇒m≤sn : ∀ {m n} → m ≤ n → m ≤ suc n
m≤n⇒m≤sn z≤n = z≤n
m≤n⇒m≤sn (s≤s leq) = s≤s (m≤n⇒m≤sn leq)

m>n⇒n≤m : ∀ {m n} → m > n → n ≤ m
m>n⇒n≤m {suc m} (s≤s m>n) = m≤n⇒m≤sn m>n

⊔-monoˡ-≤ : ∀ {ℓ₁ ℓ₂}
  → (ℓ : ℒ)
  → ℓ₁ ≼ ℓ₂
    ----------------
  → ℓ₁ ⊔ ℓ ≼ ℓ₂ ⊔ ℓ
⊔-monoˡ-≤ (l n) (≼-l {n₁} {n₂} n₁≤n₂) = ≼-l (⊔ₙ-monoˡ-≤ n n₁≤n₂)

ℓ₁≾ℓ̂→ℓ₁⊔ℓ₂≾ℓ̂⋎ℓ₂ : ∀ {ℓ̂ ℓ₁ ℓ₂}
  → (l̂ ℓ₁) ≾ ℓ̂
    -------------------------
  → l̂ (ℓ₁ ⊔ ℓ₂) ≾ ℓ̂ ⋎ (l̂ ℓ₂)
ℓ₁≾ℓ̂→ℓ₁⊔ℓ₂≾ℓ̂⋎ℓ₂ ≾-¿-r = ≾-¿-r
ℓ₁≾ℓ̂→ℓ₁⊔ℓ₂≾ℓ̂⋎ℓ₂ {l̂ ℓ} {ℓ₁} {ℓ₂} (≾-l ℓ₁≼ℓ) = ≾-l (⊔-monoˡ-≤ ℓ₂ ℓ₁≼ℓ)

ℓ≾ℓ̂→ℓ₁≼ℓ₂→ℓ⊔ℓ₁≾ℓ̂⋎ℓ₂ : ∀ {ℓ ℓ̂ ℓ₁ ℓ₂}
  → l̂ ℓ ≾ ℓ̂
  → ℓ₁ ≼ ℓ₂
    ------------------------
  → l̂ (ℓ ⊔ ℓ₁) ≾ ℓ̂ ⋎ (l̂ ℓ₂)
ℓ≾ℓ̂→ℓ₁≼ℓ₂→ℓ⊔ℓ₁≾ℓ̂⋎ℓ₂ ≾-¿-r _ = ≾-¿-r
ℓ≾ℓ̂→ℓ₁≼ℓ₂→ℓ⊔ℓ₁≾ℓ̂⋎ℓ₂ {ℓ} {l̂ ℓ′} {ℓ₁} {ℓ₂} (≾-l ℓ≼ℓ′) ℓ₁≼ℓ₂ = ≾-l (⊔-mono-≼ ℓ≼ℓ′ ℓ₁≼ℓ₂)
