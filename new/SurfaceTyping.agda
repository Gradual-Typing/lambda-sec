{- Algorithmic typing rules of the surface language -}
module SurfaceTyping where

open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import SurfaceSyntax

infix 4 _;_;_;_⊢ᴳ_⦂_

data _;_;_;_⊢ᴳ_⦂_ : Context → HeapContext → Label → StaticLabel → Term → Type → Set where

  ⊢const : ∀ {Γ Σ gc pc ι} {k : rep ι} {ℓ}
      ----------------------------------------- Const
    → Γ ; Σ ; gc ; pc ⊢ᴳ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢var : ∀ {Γ Σ gc pc A x}
    → Γ ∋ x ⦂ A
      ------------------------------ Var
    → Γ ; Σ ; gc ; pc ⊢ᴳ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ gc pc pc′ A B N ℓ}
    → (A ∷ Γ) ; Σ ; l pc′ ; low ⊢ᴳ N ⦂ B
      ------------------------------------------------------------------- Lam
    → Γ ; Σ ; gc ; pc ⊢ᴳ ƛ[ pc′ ] A ˙ N of ℓ ⦂ [ l pc′ ] A ⇒ B of l ℓ

  ⊢app : ∀ {Γ Σ gc gc′ pc A A′ B L M g p}
    → Γ ; Σ ; gc ; pc ⊢ᴳ L ⦂ [ gc′ ] A ⇒ B of g
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
    → g ≾ gc′
    → gc ≾ gc′
      -------------------------------------------- App
    → Γ ; Σ ; gc ; pc ⊢ᴳ L · M at p ⦂ stamp B g

  ⊢if : ∀ {Γ Σ gc pc A B C L M N g p}
    → Γ ; Σ ; gc     ; pc ⊢ᴳ L ⦂ ` Bool of g
    → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ᴳ M ⦂ A
    → Γ ; Σ ; gc ⋎̃ g ; pc ⊢ᴳ N ⦂ B
    → A ∨̃ B ≡ just C
      --------------------------------------------------------- If
    → Γ ; Σ ; gc ; pc ⊢ᴳ if L then M else N at p ⦂ stamp C g

  ⊢ann : ∀ {Γ Σ gc pc M A A′ p}
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ⦂ A′
    → A′ ≲ A
      --------------------------------- Ann
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ꞉ A at p ⦂ A

  ⊢ref : ∀ {Γ Σ gc pc M T g ℓ p}
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ⦂ T of g
    → T of g ≲ T of l ℓ
    → gc ≾ l ℓ
      --------------------------------------------------------------- Ref
    → Γ ; Σ ; gc ; pc ⊢ᴳ ref[ ℓ ] M at p ⦂ Ref (T of l ℓ) of l low

  ⊢deref : ∀ {Γ Σ gc pc M A g}
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ⦂ (Ref A) of g
      -------------------------------- Deref
    → Γ ; Σ ; gc ; pc ⊢ᴳ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ gc pc L M A S g g₁ p}
    → Γ ; Σ ; gc ; pc ⊢ᴳ L ⦂ Ref (S of g₁) of g
    → Γ ; Σ ; gc ; pc ⊢ᴳ M ⦂ A
    → A ≲ S of g₁
    → g ≾ g₁
    → gc ≾ g₁
      --------------------------------------------- Assign
    → Γ ; Σ ; gc ; pc ⊢ᴳ L := M at p ⦂ ` Unit of l low
