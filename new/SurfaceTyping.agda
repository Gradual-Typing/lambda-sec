{- Algorithmic typing rules of the surface language -}
module SurfaceTyping where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import SurfaceSyntax

infix 4 _;_;_⊢ᴳ_⦂_

data _;_;_⊢ᴳ_⦂_ : Context → HeapContext → Label → Term → Type → Set where

  ⊢const : ∀ {Γ Σ gc ι} {k : rep ι} {ℓ}
      -------------------------------------- Const
    → Γ ; Σ ; gc ⊢ᴳ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢var : ∀ {Γ Σ gc A x}
    → Γ ∋ x ⦂ A
      --------------------------- Var
    → Γ ; Σ ; gc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ gc pc A B N ℓ}
    → (A ∷ Γ) ; Σ ; l pc ⊢ᴳ N ⦂ B
      ------------------------------------------------------------- Lam
    → Γ ; Σ ; gc ⊢ᴳ ƛ[ pc ] A ˙ N of ℓ ⦂ [ l pc ] A ⇒ B of l ℓ

  ⊢app : ∀ {Γ Σ gc gc′ A A′ B L M g p}
    → Γ ; Σ ; gc ⊢ᴳ L ⦂ [ gc′ ] A ⇒ B of g
    → Γ ; Σ ; gc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ gc′
    → gc ≾ gc′
      --------------------------------------- App
    → Γ ; Σ ; gc ⊢ᴳ L · M at p ⦂ stamp B g

  ⊢if : ∀ {Γ Σ gc A B C L M N g p}
    → Γ ; Σ ; gc ⊢ᴳ L ⦂ ` Bool of g
    → Γ ; Σ ; gc ⋎̃ g ⊢ᴳ M ⦂ A
    → Γ ; Σ ; gc ⋎̃ g ⊢ᴳ N ⦂ B
    → A ∨̃ B ≡ just C
      ---------------------------------------------------- If
    → Γ ; Σ ; gc ⊢ᴳ if L then M else N at p ⦂ stamp C g

  ⊢ann : ∀ {Γ Σ gc M A A′ p}
    → Γ ; Σ ; gc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
      --------------------------------- Ann
    → Γ ; Σ ; gc ⊢ᴳ M ꞉ A at p ⦂ A

  ⊢ref : ∀ {Γ Σ gc M T g ℓ p}
    → Γ ; Σ ; gc ⊢ᴳ M ⦂ T of g
    → T of g ≲ T of l ℓ
    → gc ≾ l ℓ
      --------------------------------------------------------------- Ref
    → Γ ; Σ ; gc ⊢ᴳ ref[ ℓ ] M at p ⦂ Ref (T of l ℓ) of l low

  ⊢deref : ∀ {Γ Σ gc M A g}
    → Γ ; Σ ; gc ⊢ᴳ M ⦂ (Ref A) of g
      -------------------------------- Deref
    → Γ ; Σ ; gc ⊢ᴳ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ gc L M A S g g₁ p}
    → Γ ; Σ ; gc ⊢ᴳ L ⦂ Ref (S of g₁) of g
    → Γ ; Σ ; gc ⊢ᴳ M ⦂ A
    → A ≲ S of g₁
    → g ≾ g₁
    → gc ≾ g₁
      --------------------------------------------- Assign
    → Γ ; Σ ; gc ⊢ᴳ L := M at p ⦂ ` Unit of l low
