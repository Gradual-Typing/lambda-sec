module TypeBasedCast where

open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Types
open import BlameLabels

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ A B → BlameLabel → A ~ B → Cast A ⇒ B

{- Let's first consider the label parts of A ⇒ B,
   where we have four cases:
   1) ℓ ⇒ ℓ    2) ℓ ⇒ ⋆    3) ⋆ ⇒ ℓ    4) ⋆ ⇒ ⋆  -}

-- g₁ ⇒ g₂ is inert if g₁ ≢ ⋆
data Inert_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  I-label : ∀ {ℓ g₂} → Inert (l ℓ) ⇒ g₂

-- ⋆ ⇒ g₂ is active
data Active_⇒_ : ∀ (g₁ g₂ : Label) → Set where
  A-id⋆ : Active ⋆ ⇒ ⋆
  A-proj : ∀ {ℓ} → Active ⋆ ⇒ (l ℓ)

-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-base-inj : ∀ {ι ℓ}
    → (c : Cast (` ι of l ℓ) ⇒ (` ι of ⋆))
    → Inert c

  I-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    {- NOTE: We require that the casts between raw types and labels be all inert. -}
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
    → Active g₁ ⇒ g₂
      --------------------------------------
    → Active c

  A-fun-pc : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂))
    → Active gc₁ ⇒ gc₂ → Inert g₁ ⇒ g₂
      --------------------------------------
    → Active c

  A-ref : ∀ {A B g₁ g₂}
    → (c : Cast (Ref A of g₁) ⇒ (Ref B of g₂))
    → Active g₁ ⇒ g₂
      ------------------
    → Active c

active-or-inert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
{- Base -}
active-or-inert (cast (` ι of ⋆) (` ι of ⋆) p (~-ty _ ~-ι)) = inj₁ (A-base-id _)
active-or-inert (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty _ ~-ι)) = inj₁ (A-base-proj _)
active-or-inert (cast (` ι of l ℓ) (` ι of ⋆) p (~-ty _ ~-ι)) = inj₂ (I-base-inj _)
active-or-inert (cast (` ι of l low) (` ι of l low) p (~-ty l~l ~-ι)) = inj₁ (A-base-id _)
active-or-inert (cast (` ι of l high) (` ι of l high) p (~-ty h~h ~-ι)) = inj₁ (A-base-id _)
{- Ref -}
active-or-inert (cast (Ref A of ⋆) (Ref B of ⋆) p (~-ty _ (~-ref _))) = inj₁ (A-ref _ A-id⋆)
active-or-inert (cast (Ref A of ⋆) (Ref B of l ℓ₂) p (~-ty _ (~-ref _))) = inj₁ (A-ref _ A-proj)
active-or-inert (cast (Ref A of l ℓ₁) (Ref B of g₂) p (~-ty _ (~-ref _))) = inj₂ (I-ref _ I-label)
{- Fun -}
active-or-inert (cast ([ l pc ] A ⇒ B of l _) ([ gc₂ ] C ⇒ D of g₂) p (~-ty _ (~-fun _ _ _))) =
  inj₂ (I-fun _ I-label I-label)
active-or-inert (cast ([ _ ] A ⇒ B of ⋆  ) ([ _   ] C ⇒ D of ⋆  ) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun _ A-id⋆)
active-or-inert (cast ([ _ ] A ⇒ B of ⋆  ) ([ _   ] C ⇒ D of l _) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun _ A-proj)
active-or-inert (cast ([ ⋆ ] A ⇒ B of l ℓ) ([ ⋆   ] C ⇒ D of _  ) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun-pc _ A-id⋆ I-label)
active-or-inert (cast ([ ⋆ ] A ⇒ B of l ℓ) ([ l _ ] C ⇒ D of _  ) p (~-ty _ (~-fun _ _ _))) =
  inj₁ (A-fun-pc _ A-proj I-label)
