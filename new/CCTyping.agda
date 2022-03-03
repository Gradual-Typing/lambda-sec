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
    → Γ ∋ x ⦂ A
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

  ⊢let : ∀ {Γ Σ gc M N A B}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
    → (A ∷ Γ) ︔ Σ ︔ gc ⊢ N ⦂ B
      -------------------------- Let
    → Γ ︔ Σ ︔ gc ⊢ `let M N ⦂ B

  ⊢cast : ∀ {Γ Σ gc A B M} {c : Cast A ⇒ B}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
      --------------------------------------- CCCast
    → Γ ︔ Σ ︔ gc ⊢ M ⟨ c ⟩ ⦂ B

  ⊢ref : ∀ {Γ Σ M T ℓ}
    → Γ ︔ Σ ︔ l ℓ ⊢ M ⦂ T of l ℓ
      ---------------------------------------------------------- CCRef
    → Γ ︔ Σ ︔ l ℓ ⊢ ref[ ℓ ] M ⦂ (Ref (T of l ℓ)) of l low

  ⊢deref : ∀ {Γ Σ gc M A g}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ (Ref A) of g
      -------------------------------- CCDeref
    → Γ ︔ Σ ︔ gc ⊢ ! M ⦂ stamp A g

  ⊢assign : ∀ {Γ Σ L M S g}
    → Γ ︔ Σ ︔ g ⊢ L ⦂ (Ref (S of g)) of g
    → Γ ︔ Σ ︔ g ⊢ M ⦂ S of g
      --------------------------------------------- CCAssign
    → Γ ︔ Σ ︔ g ⊢ L := M ⦂ ` Unit of l low

  ⊢nsu-ref : ∀ {Γ Σ gc A M ℓ}
    → Γ ︔ Σ ︔ l ℓ ⊢ M ⦂ A
      ------------------------------ CCNSURef
    → Γ ︔ Σ ︔ gc ⊢ nsu-ref ℓ M ⦂ A

  ⊢nsu-assign : ∀ {Γ Σ gc A L M S g g₁}
    → Γ ︔ Σ ︔ gc ⊢ L ⦂ (Ref (S of g₁)) of g
    → Γ ︔ Σ ︔ g₁ ⊢ M ⦂ A
      --------------------------------- CCNSUAssign
    → Γ ︔ Σ ︔ gc ⊢ nsu-assign L M ⦂ A

  ⊢prot : ∀ {Γ Σ gc A M ℓ}
    → Γ ︔ Σ ︔ gc ⋎̃ l ℓ ⊢ M ⦂ A
      --------------------------------------- CCProt
    → Γ ︔ Σ ︔ gc ⊢ prot ℓ M ⦂ stamp A (l ℓ)

  ⊢sub : ∀ {Γ Σ gc A B M}
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ A
    → A <: B
      -------------------- CCSub
    → Γ ︔ Σ ︔ gc ⊢ M ⦂ B

  ⊢error : ∀ {Γ Σ gc A e}
      --------------------------- CCError
    → Γ ︔ Σ ︔ gc ⊢ error e ⦂ A
