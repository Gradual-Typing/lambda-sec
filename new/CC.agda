module CC where

open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_ public
open import CCTyping Cast_⇒_ public


-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-base-inj : ∀ {ι ℓ} → (c : Cast (` ι of ℓ) ⇒ (` ι of ⋆)) → Inert c
  I-fun : ∀ {A B C D gc₁ gc₂ g₁ g₂}
    → (c : Cast (([ gc₁ ] A ⇒ B) of g₁) ⇒ (([ gc₂ ] C ⇒ D) of g₂))
    → Inert c
  I-ref : ∀ {A B g₁ g₂}
    → (c : Cast ((Ref A) of g₁) ⇒ ((Ref B) of g₂))
    → Inert c

data Active : ∀ {A B} → Cast A ⇒ B → Set where
  A-base-id : ∀ {ι g} → (c : Cast (` ι of g) ⇒ (` ι of g)) → Active c
  A-base-proj : ∀ {ι ℓ} → (c : Cast (` ι of ⋆) ⇒ (` ι of l ℓ)) → Active c

active-or-inert : ∀ {A B} → (c : Cast A ⇒ B) → Active c ⊎ Inert c
active-or-inert (cast (` ι of ⋆) (` ι of ⋆) ℓ (~-ty g₁~g₂ ~-ι))           = inj₁ (A-base-id _)
active-or-inert (cast (` ι of ⋆) (` ι of l ℓ₂) ℓ (~-ty g₁~g₂ ~-ι))        = inj₁ (A-base-proj _)
active-or-inert (cast (` ι of l ℓ₁) (` ι of ⋆) ℓ (~-ty g₁~g₂ ~-ι))        = inj₂ (I-base-inj _)
active-or-inert (cast (` ι of l .low) (` ι of l .low) ℓ (~-ty l~l ~-ι))   = inj₁ (A-base-id _)
active-or-inert (cast (` ι of l .high) (` ι of l .high) ℓ (~-ty h~h ~-ι)) = inj₁ (A-base-id _)
active-or-inert (cast ((Ref A) of g₁) ((Ref B) of g₂) ℓ (~-ty g₁~g₂ (~-ref A~B))) =
  inj₂ (I-ref _)
active-or-inert (cast (([ gc₁ ] A ⇒ B) of g₁) (([ gc₂ ] C ⇒ D) of g₂) ℓ (~-ty g₁~g₂ (~-fun _ _ _))) =
  inj₂ (I-fun _)

data Value : Term → Set where
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ[ pc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B} → Value V → Inert c → Value (V ⟨ c ⟩)

-- canonical-form : ∀ {Γ Σ pc} {T V}
--   → Γ ︔ Σ ︔ pc ⊢ V ⦂ (T of ⋆)
--   → Value V
--   → ∃[ A ] ∃[ W ] Σ[ c ∈ Cast A ⇒ (T of ⋆) ] (Injection c) × (V ≡ W ⟨ c ⟩)
