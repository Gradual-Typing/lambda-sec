open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import Reduction


module TypeSafety where

data Progress (M : Term) (μ : Heap) (pc : StaticLabel) : Set where
  step : ∀ {N μ′}
    → M ∣ μ ∣ pc —→ N ∣ μ′
      ------------------------- Step
    → Progress M μ pc

  done : Value M
      ------------- Done
    → Progress M μ pc

  err : Err M
      ------------- Error
    → Progress M μ pc

progress : ∀ {Σ gc A} M → [] ; Σ ; gc ⊢ M ⦂ A → ∀ μ → Σ ⊢ μ → ∀ pc → Progress M μ pc
progress ($ k of ℓ) ⊢const μ ⊢μ pc = done V-const
progress (addr a of ℓ) (⊢addr _) μ ⊢μ pc = done V-addr
progress (` x) (⊢var ())
progress (ƛ[ _ ] A ˙ N of ℓ) (⊢lam ⊢M) μ ⊢μ pc = done V-ƛ
progress (L · M) (⊢app ⊢L ⊢M) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = □· M} L→L′)
    (done v) →
      case progress M ⊢M μ ⊢μ pc of λ where
        (step M→M′) → step (ξ {F = (L ·□) v} M→M′)
        (done w) →
          case canonical-fun ⊢L v of λ where
            Fun-ƛ → step (β w)
            (Fun-proxy v₁ i) → step (fun-cast v₁ w i)
        (err (E-error {e})) → step (ξ-err {F = (L ·□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □· M} {e = e})
progress (if L then M else N endif) (⊢if ⊢L ⊢M ⊢N) μ ⊢μ pc = {!!}
progress (`let M N) (⊢let ⊢M ⊢N) μ ⊢μ pc = {!!}
progress (M ⟨ c ⟩) (⊢cast ⊢M) μ ⊢μ pc = {!!}
progress (ref[ ℓ ] M) (⊢ref ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→M′) → step (ξ {F = ref[ ℓ ]□} M→M′)
    (done v) → step (ref v refl)
    (err (E-error {e})) → step (ξ-err {F = ref[ ℓ ]□} {e = e})
progress (! M) (⊢deref ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→M′) → step (ξ {F = !□} M→M′)
    (done v) →
      case canonical-ref ⊢M v of λ where
        Ref-addr →
          case (⊢μ (⊢addr-lookup ⊢M)) of λ where
            ⟨ T , ℓ , refl , V₁ , eq , ⊢V₁ ⟩ → step (deref eq)
        (Ref-proxy v₁ i) → step (deref-cast v₁ i)
    (err (E-error {e})) → step (ξ-err {F = !□} {e = e})
progress (L := M) (⊢assign ⊢L ⊢M) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = □:= M} L→L′)
    (done v) →
      case progress M ⊢M μ ⊢μ pc of λ where
        (step M→M′) → step (ξ {F = (L :=□) v} M→M′)
        (done w) →
          case canonical-ref ⊢L v of λ where
            Ref-addr →
              case (⊢μ (⊢addr-lookup ⊢L)) of λ where
                ⟨ T , ℓ , refl , V₁ , eq , ⊢V₁ ⟩ → step (assign w eq)
            (Ref-proxy v₁ i) → step (assign-cast v₁ w i)
        (err (E-error {e})) → step (ξ-err {F = (L :=□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □:= M} {e = e})
progress (nsu-ref ℓ M) (⊢nsu-ref ⊢M) μ ⊢μ pc =
  case pc ≼? ℓ of λ where
    (yes pc≼ℓ) → step (nsu-ref-ok pc≼ℓ)
    (no  pc⋠ℓ) → step (nsu-ref-fail pc⋠ℓ)
progress (nsu-assign L M) (⊢nsu-assign ⊢L ⊢M) μ ⊢μ pc = {!!}
progress (prot[ ℓ ] M) (⊢prot ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ (pc ⋎ ℓ) of λ where
    (step M→N) → step (prot-ctx M→N)
    (done v) → step (prot-val v)
    (err E-error) → step prot-err
progress (error e) ⊢err μ ⊢μ pc = err E-error
progress M (⊢sub ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc
