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

progress : ∀ {Σ gc A} → ∀ μ pc M → [] ; Σ ; gc ⊢ M ⦂ A → Σ ⊢ μ → Progress M μ pc
progress μ pc ($ k of ℓ) ⊢const ⊢μ = done V-const
progress μ pc (addr a of ℓ) (⊢addr _) ⊢μ = done V-addr
progress μ pc (` x) (⊢var ())
progress μ pc (ƛ[ _ ] A ˙ N of ℓ) (⊢lam ⊢M) ⊢μ = done V-ƛ
progress μ pc (L · M) (⊢app ⊢L ⊢M) ⊢μ =
  case progress μ pc L ⊢L ⊢μ of λ where
    (step L→L′) → step (ξ {F = □· M} L→L′)
    (done v) →
      case progress μ pc M ⊢M ⊢μ of λ where
        (step M→M′) → step (ξ {F = (L ·□) v} M→M′)
        (done w) →
          case canonical-fun ⊢L v of λ where
            Fun-ƛ → step (β w)
            (Fun-proxy v₁ i) → step (fun-cast v₁ w i)
        (err (E-error {e})) → step (ξ-err {F = (L ·□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □· M} {e = e})
progress μ pc (if L then M else N endif) (⊢if ⊢L ⊢M ⊢N) ⊢μ = {!!}
progress μ pc (`let M N) (⊢let ⊢M ⊢N) ⊢μ = {!!}
progress μ pc (M ⟨ c ⟩) (⊢cast ⊢M) ⊢μ = {!!}
progress μ pc (ref[ ℓ ] M) (⊢ref ⊢M) ⊢μ = {!!}
progress μ pc (! M) (⊢deref ⊢M) ⊢μ =
  case progress μ pc M ⊢M ⊢μ of λ where
    (step M→M′) → step (ξ {F = !□} M→M′)
    (done v) →
      case canonical-ref ⊢M v of λ where
        Ref-addr →
          case (⊢μ (⊢addr-lookup ⊢M)) of λ where
            ⟨ T , ℓ , refl , V₁ , eq , ⊢V₁ ⟩ → step (deref eq)
        (Ref-proxy v₁ i) → step (deref-cast v₁ i)
    (err (E-error {e})) → step (ξ-err {F = !□} {e = e})
progress μ pc (L := M) (⊢assign ⊢L ⊢M) ⊢μ = {!!}
progress μ pc (nsu-ref ℓ M) (⊢nsu-ref ⊢M) ⊢μ = {!!}
progress μ pc (nsu-assign L M) (⊢nsu-assign ⊢L ⊢M) ⊢μ = {!!}
progress μ pc (prot[ ℓ ] M) (⊢prot ⊢M) ⊢μ =
  case progress μ (pc ⋎ ℓ) M ⊢M ⊢μ of λ where
    (step M→N) → step (prot-ctx M→N)
    (done v) → step (prot-val v)
    (err E-error) → step prot-err
progress μ pc (error e) ⊢err ⊢μ = err E-error
progress μ pc M (⊢sub ⊢M _) ⊢μ = progress μ pc M ⊢M ⊢μ
