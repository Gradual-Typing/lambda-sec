module SurfaceTyping where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Data.Nat

open import Syntax
open import Utils
open import Types
open import Heap
open import SurfaceSyntax

infix 4 _︔_︔_︔_⊢ᴳ_⦂_

data _︔_︔_︔_⊢ᴳ_⦂_ : Context → HeapContext → ℕ → Label → Term → Type → Set where

  ⊢var : ∀ {Γ Σ pc A x}
    → nth Γ x ≡ just A
      ---------------------
    → Γ ︔ Σ ︔ 0 ︔ pc ⊢ᴳ ` x ⦂ A

  ⊢input : ∀ {Γ Σ pc ℓ}
    → Γ ︔ Σ ︔ 1 ︔ pc ⊢ᴳ input-of ℓ ⦂ (` 𝔹 of l ℓ)

  ⊢lam : ∀ {Γ Σ pc pc′ A B N ℓ m}
    → (A ∷ Γ) ︔ Σ ︔ m ︔ pc′ ⊢ᴳ N ⦂ B
    → Γ ︔ Σ ︔ m ︔ pc ⊢ᴳ ƛ[ pc′ ] A ˙ N of ℓ ⦂ ([ pc′ ] A ⇒ B) of l ℓ
