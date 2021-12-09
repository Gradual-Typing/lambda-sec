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

{- Note: the Nat is for the number of inputs. -}
data _︔_︔_︔_⊢ᴳ_⦂_ : Context → HeapContext → ℕ → Label → Term → Type → Set where

  ⊢var : ∀ {G Σ pc A x}
    → nth G x ≡ just A
      ---------------------------
    → G ︔ Σ ︔ 0 ︔ pc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {G Σ m pc pc′ A B N ℓ}
    → (A ∷ G) ︔ Σ ︔ m ︔ pc′ ⊢ᴳ N ⦂ B
      -----------------------------------------------------------------
    → G ︔ Σ ︔ m ︔ pc ⊢ᴳ ƛ[ pc′ ] A ˙ N of ℓ ⦂ ([ pc′ ] A ⇒ B) of l ℓ

  ⊢app : ∀ {G Σ l m pc pc′ A A′ B L M g}
    → G ︔ Σ ︔ l ︔ pc ⊢ᴳ L ⦂ ([ pc′ ] A ⇒ B) of g
    → G ︔ Σ ︔ m ︔ pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ pc′
    → pc ≾ pc′
      -----------------------------------------
    → G ︔ Σ ︔ l + m ︔ pc ⊢ᴳ L · M ⦂ stamp B g
