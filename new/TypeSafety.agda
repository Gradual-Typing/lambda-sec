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
open import Reduction

module TypeSafety where

data Error : Term → Set where
  E-error : ∀ {e : Err} → Error (err e)

data Progress (M : Term) (μ : Heap) (pc : StaticLabel) : Set where
  step : ∀ {N μ′}
    → M ∣ μ ∣ pc —→ N ∣ μ′
      ------------------------- Step
    → Progress M μ pc

  done : Value M
      ------------- Done
    → Progress M μ pc

  error : Error M
      ------------- Error
    → Progress M μ pc

progress : ∀ {Σ gc A} → ∀ μ pc M → [] ; Σ ; gc ⊢ M ⦂ A → Progress M μ pc
progress μ pc ($ k of ℓ) ⊢const = done V-const
progress μ pc (addr a of ℓ) (⊢addr _) = done V-addr
progress μ pc (` x) (⊢var ())
progress μ pc (ƛ[ _ ] A ˙ N of ℓ) (⊢lam ⊢M) = done V-ƛ
progress μ pc (L · M) (⊢app ⊢L ⊢M) =
  case progress μ pc L ⊢L of λ where
    (step L→L′) → step (ξ {F = □· M} L→L′)
    (done v) →
      case progress μ pc M ⊢M of λ where
        (step M→M′) → step (ξ {F = (L ·□) v} M→M′)
        (done w) →
          case ⟨ v , ⊢L ⟩ of λ where
            ⟨ V-ƛ , ⊢lam _ ⟩ → {!!}
        (error E-error) → {!!}
    (error (E-error {e})) → step (ξ-err {F = □· M} {e = e})
progress μ pc (if L then M else N endif) (⊢if ⊢L ⊢M ⊢N) = {!!}
progress μ pc (`let M N) (⊢let ⊢M ⊢N) = {!!}
progress μ pc (M ⟨ c ⟩) (⊢cast ⊢M) = {!!}
progress μ pc (ref[ ℓ ] M) (⊢ref ⊢M) = {!!}
progress μ pc (! M) (⊢deref ⊢M) = {!!}
progress μ pc (L := M) (⊢assign ⊢L ⊢M) = {!!}
progress μ pc (nsu-ref ℓ M) (⊢nsu-ref ⊢M) = {!!}
progress μ pc (nsu-assign L M) (⊢nsu-assign ⊢L ⊢M) = {!!}
progress μ pc (prot[ ℓ ] M) (⊢prot ⊢M) =
  case progress μ (pc ⋎ ℓ) M ⊢M of λ where
    (step M→N) → step (prot-ctx M→N)
    (done v) → step (prot-val v)
    (error E-error) → step prot-err
progress μ pc (err e) ⊢err = error E-error
progress μ pc M (⊢sub ⊢M _) = progress μ pc M ⊢M