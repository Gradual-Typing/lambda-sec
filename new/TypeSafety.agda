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
          let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ (⊢addr-lookup ⊢M) in
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
              let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ (⊢addr-lookup ⊢L) in
                step (assign w eq)
            (Ref-proxy v₁ i) → step (assign-cast v₁ w i)
        (err (E-error {e})) → step (ξ-err {F = (L :=□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □:= M} {e = e})
progress (nsu-ref ℓ M) (⊢nsu-ref ⊢M _) μ ⊢μ pc =
  case pc ≼? ℓ of λ where
    (yes pc≼ℓ) → step (nsu-ref-ok pc≼ℓ)
    (no  pc⋠ℓ) → step (nsu-ref-fail pc⋠ℓ)
progress (nsu-assign L M) (⊢nsu-assign ⊢L ⊢M) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = nsu-assign□ M} L→L′)
    (done v) →
      let ⟨ a , ℓ , eq₁ , A′ , ⊢a ⟩ = unwrap-ref ⊢L v in
      let ⟨ T , ℓ₁ , _ , V₁ , eq₂ , ⊢V₁ ⟩ = ⊢μ _ (⊢addr-lookup ⊢a) in
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
progress M (⊢sub-gc ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc


relax-Σ : ∀ {Γ Σ Σ′ gc M A}
  → Γ ; Σ ; gc ⊢ M ⦂ A
  → Σ′ ⊇ Σ
    ---------------------
  → Γ ; Σ′ ; gc ⊢ M ⦂ A
relax-Σ ⊢const Σ′⊇Σ = ⊢const
relax-Σ (⊢addr eq) Σ′⊇Σ = ⊢addr (Σ′⊇Σ _ eq)
relax-Σ (⊢var Γ∋x) Σ′⊇Σ = ⊢var Γ∋x
relax-Σ (⊢lam ⊢M) Σ′⊇Σ = ⊢lam (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢app ⊢L ⊢M) Σ′⊇Σ = ⊢app (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢if ⊢L ⊢M ⊢N) Σ′⊇Σ = ⊢if (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢let ⊢M ⊢N) Σ′⊇Σ = ⊢let (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢cast ⊢M) Σ′⊇Σ = ⊢cast (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢ref ⊢M) Σ′⊇Σ = ⊢ref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢deref ⊢M) Σ′⊇Σ = ⊢deref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢assign ⊢L ⊢M) Σ′⊇Σ = ⊢assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢nsu-ref ⊢M gc~ℓ) Σ′⊇Σ = ⊢nsu-ref (relax-Σ ⊢M Σ′⊇Σ) gc~ℓ
relax-Σ (⊢nsu-assign ⊢L ⊢M) Σ′⊇Σ = ⊢nsu-assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢prot ⊢M) Σ′⊇Σ = ⊢prot (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ ⊢err Σ′⊇Σ = ⊢err
relax-Σ (⊢sub ⊢M A<:B) Σ′⊇Σ = ⊢sub (relax-Σ ⊢M Σ′⊇Σ) A<:B
relax-Σ (⊢sub-gc ⊢M gc<:gc′) Σ′⊇Σ = ⊢sub-gc (relax-Σ ⊢M Σ′⊇Σ) gc<:gc′

plug-inversion : ∀ {Σ gc M A} {F : Frame}
  → [] ; Σ ; gc ⊢ plug M F ⦂ A
    -------------------------------------------------------------
  → ∃[ gc′ ] ∃[ B ]
       (gc <:ₗ gc′) × ([] ; Σ ; gc′ ⊢ M ⦂ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc′ ⊢ M′ ⦂ B → Σ′ ⊇ Σ → [] ; Σ′ ; gc′ ⊢ plug M′ F ⦂ A)
plug-inversion {F = □· M} (⊢app ⊢L ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V ·□) v} (⊢app ⊢V ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = ref[ ℓ ]□} (⊢ref ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref ⊢M′) ⟩
plug-inversion {F = !□} (⊢deref ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′) ⟩
plug-inversion {F = □:= M} (⊢assign ⊢L ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V :=□) v} (⊢assign ⊢V ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = let□ N} (⊢let ⊢M ⊢N) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = if□ M N} (⊢if ⊢L ⊢M ⊢N) =
  ⟨ _ , _ , <:ₗ-refl , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = □⟨ c ⟩} (⊢cast ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩
plug-inversion {F = nsu-assign□ M} (⊢nsu-assign ⊢L ⊢M) =
  ⟨ _ , _ , <:ₗ-refl , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢nsu-assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion (⊢sub ⊢M A<:B) =
  let ⟨ gc′ , B , gc<:gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢M in
    ⟨ gc′ , B , gc<:gc′ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub (wt-plug ⊢M′ Σ′⊇Σ) A<:B) ⟩
plug-inversion (⊢sub-gc ⊢plug gc<:gc′) =
  let ⟨ gc″ , B , gc′<:gc″ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug in
    ⟨ gc″ , B , <:ₗ-trans gc<:gc′ gc′<:gc″ , ⊢M , (λ ⊢M′ Σ′⊇Σ → wt-plug ⊢M′ Σ′⊇Σ) ⟩

preserve : ∀ {Σ gc M M′ A μ μ′ pc}
  → [] ; Σ ; gc ⊢ M ⦂ A
  → Σ ⊢ μ
  → M ∣ μ ∣ pc —→ M′ ∣ μ′
    ----------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
preserve ⊢plug ⊢μ (ξ {F = F} M→M′) =
  let ⟨ gc′ , B , gc<:gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug
      ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩            = preserve ⊢M ⊢μ M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub-gc (wt-plug ⊢M′ Σ′⊇Σ) gc<:gc′ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ ξ-err = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢prot ⊢V) ⊢μ (prot-val v) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢value-gc (stamp-val-wt ⊢V v) (stamp-val-value v) , ⊢μ ⟩
preserve (⊢prot ⊢M) ⊢μ (prot-ctx M→M′) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢prot ⊢M′ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ prot-err = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve (⊢app ⊢V ⊢M) ⊢μ (β v) = {!!}
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ (β-if-true {ℓ = ℓ}) =
  case const-label ⊢L of λ where
    ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
      let gc⋎ℓ<:gc⋎ℓ′ = consis-join-<:ₗ <:ₗ-refl (<:-l ℓ≼ℓ′)
          A⋎ℓ<:A⋎ℓ′   = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
        ⟨ Σ , ⊇-refl {Σ} , ⊢sub (⊢prot (⊢sub-gc ⊢M gc⋎ℓ<:gc⋎ℓ′)) A⋎ℓ<:A⋎ℓ′ , ⊢μ ⟩
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ (β-if-false {ℓ = ℓ}) =
  case const-label ⊢L of λ where
    ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
      let gc⋎ℓ<:gc⋎ℓ′ = consis-join-<:ₗ <:ₗ-refl (<:-l ℓ≼ℓ′)
          A⋎ℓ<:A⋎ℓ′   = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
        ⟨ Σ , ⊇-refl {Σ} , ⊢sub (⊢prot (⊢sub-gc ⊢N gc⋎ℓ<:gc⋎ℓ′)) A⋎ℓ<:A⋎ℓ′ , ⊢μ ⟩
preserve ⊢M ⊢μ (β-let x) = {!!}
preserve ⊢M ⊢μ (ref x x₁) = {!!}
preserve {Σ} (⊢nsu-ref ⊢M gc~ℓ) ⊢μ (nsu-ref-ok pc≼ℓ) =
  ⟨ Σ , ⊇-refl {Σ} , {!!} , ⊢μ ⟩
preserve ⊢M ⊢μ (nsu-ref-fail x) = {!!}
preserve ⊢M ⊢μ (deref x) = {!!}
preserve ⊢M ⊢μ (assign x x₁) = {!!}
preserve {Σ} (⊢nsu-assign ⊢L ⊢M) ⊢μ (nsu-assign-ok w eq1 eq2 pc≼ℓ₁) =
  ⟨ Σ , ⊇-refl {Σ} , {!!} , ⊢μ ⟩
preserve ⊢M ⊢μ (nsu-assign-fail w x x₁ x₂) = {!!}
preserve ⊢M ⊢μ (cast ⊢V v a) = {!!}
preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ (if-cast-true i) = {!!}
preserve ⊢M ⊢μ (if-cast-false x) = {!!}
preserve {Σ} (⊢app ⊢V ⊢W) ⊢μ (fun-cast v w i) =
  ⟨ Σ , ⊇-refl {Σ} , {!!} , ⊢μ ⟩
preserve ⊢M ⊢μ (deref-cast x x₁) = {!!}
preserve ⊢M ⊢μ (assign-cast x x₁ x₂) = {!!}
preserve (⊢sub ⊢M A<:B) ⊢μ R =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ R in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢M′ A<:B , ⊢μ′ ⟩
preserve (⊢sub-gc ⊢M gc<:gc′) ⊢μ M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub-gc ⊢M′ gc<:gc′ , ⊢μ′ ⟩
