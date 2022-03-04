module TypeBasedCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types
open import BlameLabels

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ A B → BlameLabel → A ~ B → Cast A ⇒ B

{- Let's first consider the label parts of A ⇒ B,
   where we have four cases:
   1) ℓ ⇒ ℓ    2) ℓ ⇒ ⋆    3) ⋆ ⇒ ℓ    4) ⋆ ⇒ ⋆  -}

-- g₁ ⇒ g₂ is inert if g₁ ≢ ⋆
data Inert_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  I-id  : ∀ {ℓ} → Inert l ℓ ⇒ l ℓ
  I-inj : ∀ {ℓ} → Inert l ℓ ⇒ ⋆

-- ⋆ ⇒ g₂ is active
data Active_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  A-id   : Active ⋆ ⇒ ⋆
  A-proj : ∀ {ℓ} → Active ⋆ ⇒ l ℓ

-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-base-inj : ∀ {ι ℓ}
    → (c : Cast (` ι of l ℓ) ⇒ (` ι of ⋆))
    → Inert c

  I-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂))
    → Inert gc₁ ⇒ gc₂ → Inert g₁ ⇒ g₂
      -------------------------------------
    → Inert c

  I-ref : ∀ {A B g₁ g₂}
    → (c : Cast (Ref A of g₁) ⇒ (Ref B of g₂))
    → Inert g₁ ⇒ g₂
      -----------------
    → Inert c

data Active : ∀ {A B} → Cast A ⇒ B → Set where
  A-base-id : ∀ {ι g}
    → (c : Cast (` ι of g) ⇒ (` ι of g))
    → Active c

  A-base-proj : ∀ {ι ℓ}
    → (c : Cast (` ι of ⋆) ⇒ (` ι of l ℓ))
    → Active c

  A-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂))
    → Active gc₁ ⇒ gc₂ ⊎ Active g₁ ⇒ g₂
      --------------------------------------
    → Active c

  A-ref : ∀ {A B g₁ g₂}
    → (c : Cast (Ref A of g₁) ⇒ (Ref B of g₂))
    → Active g₁ ⇒ g₂
      ------------------
    → Active c

-- active-or-inert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
