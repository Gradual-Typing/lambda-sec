module CC where

open import Data.List
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_ public
open import CCTyping Cast_⇒_ public


data Injection : ∀ {A B} → Cast A ⇒ B → Set where
  inj : ∀ {S T g} → (c : Cast (S of g) ⇒ (T of ⋆)) → g ≢ ⋆ → Injection c

-- Value forming cast
data Inert : ∀ {A B} → Cast A ⇒ B → Set where
  I-inj : ∀ {A B} {c : Cast A ⇒ B} → Injection c → Inert c

data Value : Term → Set where
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ[ pc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B} → Value V → Inert c → Value (V ⟨ c ⟩)

-- canonical-form : ∀ {Γ Σ pc} {T V}
--   → Γ ︔ Σ ︔ pc ⊢ V ⦂ (T of ⋆)
--   → Value V
--   → ∃[ A ] ∃[ W ] Σ[ c ∈ Cast A ⇒ (T of ⋆) ] (Injection c) × (V ≡ W ⟨ c ⟩)
