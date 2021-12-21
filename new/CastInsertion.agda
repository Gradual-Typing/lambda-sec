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

compile : ∀ {Γ Σ gc A} (M : Term) → Γ ︔ Σ ︔ gc ⊢ᴳ M ⦂ A → CCTerm
compile ($ᴳ k of ℓ) ⊢const = $ k of ℓ
compile (`ᴳ x) (⊢var x∈Γ) = ` x
compile (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = ƛ[ pc ] A ˙ compile N ⊢N of ℓ
compile (L · M at p) (⊢app {gc = gc} {gc′} {A} {A′} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′) =
  case ≲-prop A′≲A of λ where
    ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ →
      {- Insert `# static` if gc , gc′, and g are all static, `# dyn` otherwise -}
      case ⟨ gc , ⟨ gc′ , g ⟩ ⟩ of λ where
        ⟨ l _ , ⟨ l _ , l _ ⟩ ⟩ →
             (compile L ⊢L) · (compile M ⊢M ⟨ cast A′ B p A′~B ⟩) # static
        _ → (compile L ⊢L) · (compile M ⊢M ⟨ cast A′ B p A′~B ⟩) # dyn
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
compile (ref[ ℓ ] M at p) (⊢ref {gc = gc} {T = T} {g} ⊢M Tg≲Tℓ gc≾ℓ) =
  case ≲-prop Tg≲Tℓ of λ where
    ⟨ A , ⟨ Tg~A , A<:Tℓ ⟩ ⟩ →
      {- Insert `# static` if gc is static and `# dyn` otherwise -}
      case gc of λ where
        (l _) → ref[ ℓ ] (compile M ⊢M ⟨ cast (T of g) A p Tg~A ⟩) # static
        ⋆     → ref[ ℓ ] (compile M ⊢M ⟨ cast (T of g) A p Tg~A ⟩) # dyn
compile (!ᴳ M) (⊢deref ⊢M) = ! (compile M ⊢M)
compile (L := M at p) (⊢assign {gc = gc} {A = A} {g = g} {g₁} ⊢L ⊢M A≲Sg1 g≾g1 gc≾g1) =
  case ≲-prop A≲Sg1 of λ where
    ⟨ B , ⟨ A~B , B<:Sg1 ⟩ ⟩ →
      {- Insert `# static` if gc , g, and g₁ are all static, `# dyn` otherwise -}
      case ⟨ gc , ⟨ g , g₁ ⟩ ⟩ of λ where
        ⟨ l _ , ⟨ l _ , l _ ⟩ ⟩ →
             (compile L ⊢L) := (compile M ⊢M ⟨ cast A B p A~B ⟩) # static
        _ → (compile L ⊢L) := (compile M ⊢M ⟨ cast A B p A~B ⟩) # dyn


compile-preserve : ∀ {Γ Σ gc A} (M : Term)
  → (⊢M : Γ ︔ Σ ︔ gc ⊢ᴳ M ⦂ A)
  → Γ ︔ Σ ︔ gc ⊢ compile M ⊢M ⦂ A
compile-preserve ($ᴳ k of ℓ) ⊢const = ⊢const
compile-preserve (`ᴳ x) (⊢var x∈Γ) = ⊢var x∈Γ
compile-preserve (ƛᴳ[ pc ] A ˙ N of ℓ) (⊢lam ⊢N) = ⊢lam (compile-preserve N ⊢N)
compile-preserve (L · M at p) (⊢app {gc = gc} {gc′} {g = g} ⊢L ⊢M A′≲A g≾gc′ gc≾gc′)
  with ≲-prop A′≲A
... | ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩
  with gc | gc′ | g
... | ⋆   | _   | _ = ⊢app-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A)
... | l _ | ⋆   | _ = ⊢app-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A)
... | l _ | l _ | ⋆ = ⊢app-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A)
... | l pc | l pc′ | l ℓ =
  case ⟨ g≾gc′ , gc≾gc′ ⟩ of λ where
    ⟨ ≾-l ℓ≼pc′ , ≾-l pc≼pc′ ⟩ →
      ⊢app (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A) ℓ≼pc′ pc≼pc′
compile-preserve (if L then M else N at p) (⊢if {A = A} {B} {C} ⊢L ⊢M ⊢N A∨̃B≡C)
  with consis-join-≲ {A} {B} A∨̃B≡C
... | ⟨ A≲C , B≲C ⟩
  with ≲-prop A≲C | ≲-prop B≲C
... | ⟨ A′ , ⟨ A~A′ , A′<:C ⟩ ⟩ | ⟨ B′ , ⟨ B~B′ , B′<:C ⟩ ⟩ =
  ⊢if (compile-preserve L ⊢L)
      (⊢sub (⊢cast (compile-preserve M ⊢M)) A′<:C)
      (⊢sub (⊢cast (compile-preserve N ⊢N)) B′<:C)
compile-preserve {Γ} {Σ} {pc} {A} (M ꞉ A at p) (⊢ann {A′ = A′} ⊢M A′≲A)
  with ≲-prop A′≲A
... | ⟨ B , ⟨ A′~B , B<:A ⟩ ⟩ = ⊢sub (⊢cast (compile-preserve M ⊢M)) B<:A
compile-preserve (ref[ ℓ ] M at p) (⊢ref {gc = gc} ⊢M Tg≲Tℓ gc≾ℓ)
  with ≲-prop Tg≲Tℓ
... | ⟨ A , ⟨ Tg~A , A<:Tℓ ⟩ ⟩
  with gc
...   | ⋆ = ⊢ref-dyn (⊢sub (⊢cast (compile-preserve M ⊢M)) A<:Tℓ)
...   | l pc =
  case gc≾ℓ of λ where
    (≾-l pc≼ℓ) → ⊢ref (⊢sub (⊢cast (compile-preserve M ⊢M)) A<:Tℓ) pc≼ℓ
compile-preserve (!ᴳ M) (⊢deref ⊢M) = ⊢deref (compile-preserve M ⊢M)
compile-preserve (L := M at p) (⊢assign {gc = gc} {g = g} {g₁} ⊢L ⊢M A≲Sg1 g≾g1 gc≾g1)
  with ≲-prop A≲Sg1
... | ⟨ B , ⟨ A~B , B<:Sg1 ⟩ ⟩
  with gc | g | g₁
... | ⋆   | _   | _ = ⊢assign-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Sg1)
... | l _ | ⋆   | _ = ⊢assign-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Sg1)
... | l _ | l _ | ⋆ = ⊢assign-dyn (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Sg1)
... | l pc | l ℓ | l ℓ₁ =
  case ⟨ g≾g1 , gc≾g1 ⟩ of λ where
    ⟨ ≾-l ℓ≼ℓ₁ , ≾-l pc≼ℓ₁ ⟩ →
      ⊢assign (compile-preserve L ⊢L) (⊢sub (⊢cast (compile-preserve M ⊢M)) B<:Sg1) ℓ≼ℓ₁ pc≼ℓ₁
