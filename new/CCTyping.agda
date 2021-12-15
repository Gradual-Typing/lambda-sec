{- Typing rules of the cast calculus -}

open import Types

module CCTyping (Cast_⇒_ : Type → Type → Set) where

open import Data.Nat
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Syntax
open import Utils
open import Types
open import CCSyntax Cast_⇒_

infix 4 _︔_︔_⊢_⦂_

data _︔_︔_⊢_⦂_ : Context → HeapContext → Label → Term → Type → Set where

  ⊢const : ∀ {Γ Σ pc ι} {k : rep ι} {ℓ}
      -------------------------------------- CCConst
    → Γ ︔ Σ ︔ pc ⊢ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢addr : ∀ {Γ Σ pc A a ℓ}
    → key _≟_ Σ a ≡ just A
      ------------------------------------------ CCAddr
    → Γ ︔ Σ ︔ pc ⊢ addr a of ℓ ⦂ Ref A of l ℓ

  ⊢var : ∀ {Γ Σ pc A x}
    → nth Γ x ≡ just A
      --------------------------- CCVar
    → Γ ︔ Σ ︔ pc ⊢ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ pc pc′ A B N ℓ}
    → (A ∷ Γ) ︔ Σ ︔ pc′ ⊢ N ⦂ B
      ------------------------------------------------------------- CCLam
    → Γ ︔ Σ ︔ pc ⊢ ƛ[ pc′ ] A ˙ N of ℓ ⦂ ([ pc′ ] A ⇒ B) of l ℓ

  ⊢app : ∀ {Γ Σ pc A B L M}
    → Γ ︔ Σ ︔ pc ⊢ L ⦂ ([ pc ] A ⇒ B) of pc
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ A
      --------------------------------- CCApp
    → Γ ︔ Σ ︔ pc ⊢ L · M ⦂ stamp B pc

  ⊢if : ∀ {Γ Σ pc A L M N g}
    → Γ ︔ Σ ︔ pc ⊢ L ⦂ ` Bool of g
    → Γ ︔ Σ ︔ pc ⋎̃ g ⊢ M ⦂ A
    → Γ ︔ Σ ︔ pc ⋎̃ g ⊢ N ⦂ A
      ---------------------------------------------------- CCIf
    → Γ ︔ Σ ︔ pc ⊢ if L then M else N endif ⦂ stamp A g

  ⊢cast : ∀ {Γ Σ pc A B M} {c : Cast A ⇒ B}
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ A
      --------------------------------------- CCCast
    → Γ ︔ Σ ︔ pc ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ref : ∀ {Γ Σ pc M S}
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ S of pc
      ---------------------------------------------------------- CCRef
    → Γ ︔ Σ ︔ pc ⊢ ref[ S of pc ] M ⦂ (Ref (S of pc)) of l low

  ⊢deref : ∀ {Γ Σ pc M A g}
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ (Ref A) of g
      -------------------------------- CCDeref
    → Γ ︔ Σ ︔ pc ⊢ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ pc L M S}
    → Γ ︔ Σ ︔ pc ⊢ L ⦂ (Ref (S of pc)) of pc
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ S of pc
      ----------------------------------------- CCAssign
    → Γ ︔ Σ ︔ pc ⊢ L := M ⦂ ` Unit of l low

  ⊢sub : ∀ {Γ Σ pc A B M}
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ A
    → A <: B
      -------------------- CCSub
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ B

  ⊢sub-pc : ∀ {Γ Σ pc pc′ A M}
    → Γ ︔ Σ ︔ pc′ ⊢ M ⦂ A
    → pc <:ₗ pc′
      -------------------------- CCSubPC
    → Γ ︔ Σ ︔ pc ⊢ M ⦂ A

