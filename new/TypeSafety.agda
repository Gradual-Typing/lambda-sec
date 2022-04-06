open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
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
progress (if L then M else N endif) (⊢if {g = g} ⊢L ⊢M ⊢N) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = if□ M N} L→L′)
    (done v) →
      case canonical-bool ⊢L v of λ where
        Bool-true → step β-if-true
        Bool-false → step β-if-false
        (Bool-cast {true} i) → step (if-cast-true i)
        (Bool-cast {false} i) → step (if-cast-false i)
    (err (E-error {e})) → step (ξ-err {F = if□ M N} {e = e})
progress (`let M N) (⊢let ⊢M ⊢N) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→M′) → step (ξ {F = let□ N} M→M′)
    (done v) → step (β-let v)
    (err (E-error {e})) → step (ξ-err {F = let□ N} {e = e})
progress (M ⟨ c ⟩) (⊢cast ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→M′) → step (ξ {F = □⟨ c ⟩} M→M′)
    (done v) →
      case active-or-inert c of λ where
        (inj₁ a) → step (cast ⊢M v a)
        (inj₂ i) → done (V-cast v i)
    (err (E-error {e})) → step (ξ-err {F = □⟨ c ⟩} {e = e})
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
          let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ (⊢addr-lookup ⊢M) in
            step (deref eq)
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
              let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ (⊢addr-lookup ⊢L) in
                step (assign w eq)
            (Ref-proxy v₁ i) → step (assign-cast v₁ w i)
        (err (E-error {e})) → step (ξ-err {F = (L :=□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □:= M} {e = e})
progress (nsu-ref ℓ M) (⊢nsu-ref ⊢M) μ ⊢μ pc =
  case pc ≼? ℓ of λ where
    (yes pc≼ℓ) → step (nsu-ref-ok pc≼ℓ)
    (no  pc⋠ℓ) → step (nsu-ref-fail pc⋠ℓ)
progress (nsu-assign L M) (⊢nsu-assign ⊢L ⊢M) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = nsu-assign□ M} L→L′)
    (done v) →
      let ⟨ a , ℓ , eq₁ , A′ , ⊢a ⟩ = unwrap-ref ⊢L v in
      let ⟨ T , ℓ₁ , _ , V₁ , eq₂ , ⊢V₁ ⟩ = ⊢μ (⊢addr-lookup ⊢a) in
        case pc ≼? ℓ₁ of λ where
          (yes pc≼ℓ₁) → step (nsu-assign-ok v eq₁ eq₂ pc≼ℓ₁)
          (no  pc⋠ℓ₁) → step (nsu-assign-fail v eq₁ eq₂ pc⋠ℓ₁)
    (err (E-error {e})) → step (ξ-err {F = nsu-assign□ M} {e = e})
progress (prot[ ℓ ] M) (⊢prot ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ (pc ⋎ ℓ) of λ where
    (step M→N) → step (prot-ctx M→N)
    (done v) → step (prot-val v)
    (err E-error) → step prot-err
progress (error e) ⊢err μ ⊢μ pc = err E-error
progress M (⊢sub ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc


preserve : ∀ {Σ gc M M′ A μ μ′ pc}
  → [] ; Σ ; gc ⊢ M ⦂ A
  → Σ ⊢ μ
  → M ∣ μ ∣ pc —→ M′ ∣ μ′
    ----------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
preserve ⊢M ⊢μ R = {!!}
