module TypeBasedCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Types
open import BlameLabels

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ A B → BlameLabel → A ~ B → Cast A ⇒ B

-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-base-inj : ∀ {ι ℓ}
    → (c : Cast (` ι of ℓ) ⇒ (` ι of ⋆))
    → Inert c

  I-fun-inj : ∀ {A B C D gc₁ gc₂ ℓ}
    → (c : Cast ([ gc₁ ] A ⇒ B of ℓ) ⇒ ([ gc₂ ] C ⇒ D of ⋆))
    → Inert c

  I-ref-inj : ∀ {A B ℓ}
    → (c : Cast (Ref A of ℓ) ⇒ (Ref B of ⋆))
    → Inert c

-- FIXME
data Active : ∀ {A B} → Cast A ⇒ B → Set where
  A-base-id : ∀ {ι g}
    → (c : Cast (` ι of g) ⇒ (` ι of g))
    → Active c

  A-base-proj : ∀ {ι ℓ}
    → (c : Cast (` ι of ⋆) ⇒ (` ι of l ℓ))
    → Active c

-- active-or-inert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
