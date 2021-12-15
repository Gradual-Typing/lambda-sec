module CastInsertion where

open import Data.Nat
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import BlameLabels
open import Types
open import TypeBasedCast
open import SurfaceLang
open import CC renaming (Term to CCTerm)

compile : ∀ {Γ Σ pc A} (M : Term) → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A → CCTerm
compile ($ k of ℓ) ⊢const = {!!}
compile (` x) (⊢var x∈Γ) = {!!}
compile (ƛ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = {!!}
compile (L · M) (⊢app ⊢L ⊢M A′≲A g≾pc′ pc≾pc′) = {!!}
compile (if L then M else N endif) (⊢if ⊢L ⊢M ⊢N eq) = {!!}
compile (M ꞉ A) (⊢ann {A′ = A′} ⊢M A′≲A) =
  case ≲-prop A′≲A of λ where
    ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ →
      compile M ⊢M ⟨ cast A′ B (pos 0) A′~B ⟩
compile (ref (T of g) M) (⊢ref ⊢M x x₁) = {!!}
compile (! M) (⊢deref ⊢M) = {!!}
compile (L := M) (⊢assign ⊢M ⊢M₁ x x₁ x₂) = {!!}
