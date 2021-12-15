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
  renaming (`_ to `ᴳ_;
            $_of_ to $ᴳ_of_;
            ƛ[_]_˙_of_ to ƛᴳ[_]_˙_of_)
open import CC renaming (Term to CCTerm)

compile : ∀ {Γ Σ pc A} (M : Term) → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k of ℓ
compile (`ᴳ x) (⊢var x∈Γ) = ` x
compile (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = {!!}
compile (L · M at p) (⊢app ⊢L ⊢M A′≲A g≾pc′ pc≾pc′) = {!!}
compile (if L then M else N at p) (⊢if ⊢L ⊢M ⊢N eq) = {!!}
compile (M ꞉ A at p) (⊢ann {A′ = A′} ⊢M A′≲A) =
  case ≲-prop A′≲A of λ where
    ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ →
      compile M ⊢M ⟨ cast A′ B p A′~B ⟩
compile (ref[ T of g ] M at p) (⊢ref ⊢M A≲Sg pc≾g) = {!!}
compile (! M) (⊢deref ⊢M) = {!!}
compile (L := M at p) (⊢assign ⊢L ⊢M A≲Sg1 g≾g1 pc≾g1) = {!!}
