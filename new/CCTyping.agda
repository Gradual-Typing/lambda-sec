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

  ⊢const : ∀ {Γ Σ gc ι} {k : rep ι} {ℓ}
      -------------------------------------- CCConst
    → Γ ︔ Σ ︔ gc ⊢ $ k of ℓ ⦂ ` ι of l ℓ

  ⊢addr : ∀ {Γ Σ gc A a ℓ}
    → key _≟_ Σ a ≡ just A
      ------------------------------------------ CCAddr
    → Γ ︔ Σ ︔ gc ⊢ addr a of ℓ ⦂ Ref A of l ℓ

  ⊢var : ∀ {Γ Σ gc A x}
    → nth Γ x ≡ just A
      --------------------------- CCVar
    → Γ ︔ Σ ︔ gc ⊢ ` x ⦂ A

  ⊢lam : ∀ {Γ Σ gc pc A B N ℓ}
    → (A ∷ Γ) ︔ Σ ︔ (l pc) ⊢ N ⦂ B
      ------------------------------------------------------------- CCLam
    → Γ ︔ Σ ︔ gc ⊢ ƛ[ pc ] A ˙ N of ℓ ⦂ ([ l pc ] A ⇒ B) of l ℓ

  ⊢app : ∀ {Γ Σ gc A B L M g}
    → Γ ︔ Σ ︔ gc ⊢ L ⦂ ([ gc ⋎̃ g ] A ⇒ B) of g
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
      --------------------------------------- CCApp
    → Γ ︔ Σ ︔ gc ⊢ L · M ⦂ stamp B g

  ⊢if : ∀ {Γ Σ gc A L M N g}
    → Γ ︔ Σ ︔ gc ⊢ L ⦂ ` Bool of g
    → Γ ︔ Σ ︔ gc ⋎̃ g ⊢ M ⦂ A
    → Γ ︔ Σ ︔ gc ⋎̃ g ⊢ N ⦂ A
      ---------------------------------------------------- CCIf
    → Γ ︔ Σ ︔ gc ⊢ if L then M else N endif ⦂ stamp A g

  ⊢cast : ∀ {Γ Σ gc A B M} {c : Cast A ⇒ B}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
      --------------------------------------- CCCast
    → Γ ︔ Σ ︔ gc ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ref : ∀ {Γ Σ pc M T ℓ}
    → Γ ︔ Σ ︔ (l pc) ⊢ M ⦂ T of l ℓ
    → pc ≼ ℓ
      ---------------------------------------------------------- CCRef
    → Γ ︔ Σ ︔ (l pc) ⊢ ref[ ℓ ] M # static ⦂ (Ref (T of l ℓ)) of l low

  ⊢ref-dyn : ∀ {Γ Σ gc M T ℓ}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ T of l ℓ
      ---------------------------------------------------------- CCRefDyn
    → Γ ︔ Σ ︔ gc ⊢ ref[ ℓ ] M # dyn ⦂ (Ref (T of l ℓ)) of l low

  ⊢deref : ∀ {Γ Σ gc M A g}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ (Ref A) of g
      -------------------------------- CCDeref
    → Γ ︔ Σ ︔ gc ⊢ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ pc L M S ℓ}
    → Γ ︔ Σ ︔ (l pc) ⊢ L ⦂ (Ref (S of l ℓ)) of l ℓ
    → Γ ︔ Σ ︔ (l pc) ⊢ M ⦂ S of l ℓ
    → pc ≼ ℓ
      --------------------------------------------- CCAssign
    → Γ ︔ Σ ︔ (l pc) ⊢ L := M # static ⦂ ` Unit of l low

  ⊢assign-dyn : ∀ {Γ Σ gc L M S g g₁}
    → Γ ︔ Σ ︔ gc ⊢ L ⦂ (Ref (S of g₁)) of g
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ S of g₁
      --------------------------------------------- CCAssignDyn
    → Γ ︔ Σ ︔ gc ⊢ L := M # dyn ⦂ ` Unit of l low

  ⊢sub : ∀ {Γ Σ gc A B M}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
    → A <: B
      -------------------- CCSub
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ B
