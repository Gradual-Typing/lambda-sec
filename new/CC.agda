module CC where

open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
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

data Value : Term → Set where
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ[ pc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B} → Value V → Inert c → Value (V ⟨ c ⟩)

-- canonical-form : ∀ {Γ Σ pc} {T V}
--   → Γ ︔ Σ ︔ pc ⊢ V ⦂ (T of ⋆)
--   → Value V
--   → ∃[ A ] ∃[ W ] Σ[ c ∈ Cast A ⇒ (T of ⋆) ] (Injection c) × (V ≡ W ⟨ c ⟩)
