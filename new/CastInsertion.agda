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
            ƛ[_]_˙_of_ to ƛᴳ[_]_˙_of_;
            !_ to !ᴳ_)
open import CC renaming (Term to CCTerm)

compile : ∀ {Γ Σ pc A} (M : Term) → Γ ︔ Σ ︔ pc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k of ℓ
compile (`ᴳ x) (⊢var x∈Γ) = ` x
compile (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = ƛ[ pc ] A ˙ compile N ⊢N of ℓ
compile (L · M at p) (⊢app {A′ = A′} ⊢L ⊢M A′≲A g≾pc′ pc≾pc′) =
  case ≲-prop A′≲A of λ where
    ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ →
      (compile L ⊢L) · (compile M ⊢M ⟨ cast A′ B p A′~B ⟩)
compile (if L then M else N at p) (⊢if {A = A} {B} {C} ⊢L ⊢M ⊢N A∨̃B≡C) =
  case consis-join-≲ {A} {B} A∨̃B≡C of λ where
    ⟨ A≲C , B≲C ⟩ →
      case ⟨ ≲-prop A≲C , ≲-prop B≲C ⟩ of λ where
        ⟨ ⟨ A′ , ⟨ A~A′ , A′<:C ⟩ ⟩ , ⟨ B′ , ⟨ B~B′ , B′<:C ⟩ ⟩ ⟩ →
          if (compile L ⊢L)
            then (compile M ⊢M ⟨ cast A A′ p A~A′ ⟩)
            else (compile N ⊢N ⟨ cast B B′ p B~B′ ⟩)
          endif
compile (M ꞉ A at p) (⊢ann {A′ = A′} ⊢M A′≲A) =
  case ≲-prop A′≲A of λ where
    ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ →
      compile M ⊢M ⟨ cast A′ B p A′~B ⟩
compile (ref[ S of g ] M at p) (⊢ref {A = A} ⊢M A≲Sg pc≾g) =
  case ≲-prop A≲Sg of λ where
    ⟨ B , ⟨ A~B , B<:Sg ⟩ ⟩ →
      ref[ S of g ] (compile M ⊢M ⟨ cast A B p A~B ⟩)
compile (!ᴳ M) (⊢deref ⊢M) = ! (compile M ⊢M)
compile (L := M at p) (⊢assign {A = A} ⊢L ⊢M A≲Sg1 g≾g1 pc≾g1) =
  case ≲-prop A≲Sg1 of λ where
    ⟨ B , ⟨ A~B , B<:Sg1 ⟩ ⟩ →
      (compile L ⊢L) := (compile M ⊢M ⟨ cast A B p A~B ⟩)
