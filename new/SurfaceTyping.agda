{- Algorithmic typing rules of the surface language -}
module SurfaceTyping where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import SurfaceSyntax

infix 4 _︔_︔_⊢ᴳ_⦂_

data _︔_︔_⊢ᴳ_⦂_ : Context → HeapContext → Label → Term → Type → Set where

  ⊢const : ∀ {Γ Σ pc ι} {k : rep ι} {ℓ}
      -------------------------------------- Const
    → Γ ︔ Σ ︔ pc ⊢ᴳ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢var : ∀ {Γ Σ pc A x}
    → nth Γ x ≡ just A
      --------------------------- Var
    → Γ ︔ Σ ︔ pc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ pc pc′ A B N ℓ}
    → (A ∷ Γ) ︔ Σ ︔ pc′ ⊢ᴳ N ⦂ B
      ------------------------------------------------------------- Lam
    → Γ ︔ Σ ︔ pc ⊢ᴳ ƛ[ pc′ ] A ˙ N of ℓ ⦂ ([ pc′ ] A ⇒ B) of l ℓ

  ⊢app : ∀ {Γ Σ pc pc′ A A′ B L M g p}
    → Γ ︔ Σ ︔ pc ⊢ᴳ L ⦂ ([ pc′ ] A ⇒ B) of g
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ pc′
    → pc ≾ pc′
      --------------------------------------- App
    → Γ ︔ Σ ︔ pc ⊢ᴳ L · M at p ⦂ stamp B g

  ⊢if : ∀ {Γ Σ pc A B C L M N g p}
    → Γ ︔ Σ ︔ pc ⊢ᴳ L ⦂ ` Bool of g
    → Γ ︔ Σ ︔ pc ⋎̃ g ⊢ᴳ M ⦂ A
    → Γ ︔ Σ ︔ pc ⋎̃ g ⊢ᴳ N ⦂ B
    → A ∨̃ B ≡ just C
      ---------------------------------------------------- If
    → Γ ︔ Σ ︔ pc ⊢ᴳ if L then M else N at p ⦂ stamp C g

  ⊢ann : ∀ {Γ Σ pc M A A′ p}
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
      --------------------------------- Ann
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ꞉ A at p ⦂ A

  ⊢ref : ∀ {Γ Σ pc M A S g p}
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A
    → A ≲ S of g
    → pc ≾ g
      --------------------------------------------------------------- Ref
    → Γ ︔ Σ ︔ pc ⊢ᴳ ref[ S of g ] M at p ⦂ (Ref (S of g)) of l low

  ⊢deref : ∀ {Γ Σ pc M A g}
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ (Ref A) of g
      -------------------------------- Deref
    → Γ ︔ Σ ︔ pc ⊢ᴳ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ pc L M A S g g₁ p}
    → Γ ︔ Σ ︔ pc ⊢ᴳ L ⦂ (Ref (S of g₁)) of g
    → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A
    → A ≲ S of g₁
    → g ≾ g₁
    → pc ≾ g₁
      --------------------------------------------- Assign
    → Γ ︔ Σ ︔ pc ⊢ᴳ L := M at p ⦂ ` Unit of l low