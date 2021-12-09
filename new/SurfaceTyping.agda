module SurfaceTyping where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import Heap
open import SurfaceSyntax

infix 4 _︔_︔_⊢ᴳ_⦂_

data _︔_︔_⊢ᴳ_⦂_ : Context → HeapContext → Label → Term → Type → Set where

  ⊢var : ∀ {G Σ pc A x}
    → nth G x ≡ just A
      ---------------------------
    → G ︔ Σ ︔ pc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {G Σ pc pc′ A B N ℓ}
    → (A ∷ G) ︔ Σ ︔ pc′ ⊢ᴳ N ⦂ B
      -----------------------------------------------------------------
    → G ︔ Σ ︔ pc ⊢ᴳ ƛ[ pc′ ] A ˙ N of ℓ ⦂ ([ pc′ ] A ⇒ B) of l ℓ

  ⊢app : ∀ {G Σ pc pc′ A A′ B L M g}
    → G ︔ Σ ︔ pc ⊢ᴳ L ⦂ ([ pc′ ] A ⇒ B) of g
    → G ︔ Σ ︔ pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ pc′
    → pc ≾ pc′
      -----------------------------------------
    → G ︔ Σ ︔ pc ⊢ᴳ L · M ⦂ stamp B g
