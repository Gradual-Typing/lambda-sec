open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
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
            (Fun-ƛ _ _) → step (β w)
            (Fun-proxy f i _) → step (fun-cast (fun-is-value f) w i)
        (err (E-error {e})) → step (ξ-err {F = (L ·□) v} {e = e})
    (err (E-error {e})) → step (ξ-err {F = □· M} {e = e})
progress (if L then M else N endif) (⊢if {g = g} ⊢L ⊢M ⊢N) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = if□ M N} L→L′)
    (done v) →
      case canonical-const ⊢L v of λ where
        (Const-base {𝔹} {true})   → step β-if-true
        (Const-base {𝔹} {false})  → step β-if-false
        (Const-inj {𝔹} {true} _)  → step (if-cast-true (I-base-inj _))
        (Const-inj {𝔹} {false} _) → step (if-cast-false (I-base-inj _))
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
        (Ref-addr eq _) →
          let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ eq in
            step (deref eq)
        (Ref-proxy r i _) → step (deref-cast (ref-is-value r) i)
    (err (E-error {e})) → step (ξ-err {F = !□} {e = e})
progress (L := M) (⊢assign ⊢L ⊢M) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = □:= M} L→L′)
    (done v) →
      case progress M ⊢M μ ⊢μ pc of λ where
        (step M→M′) → step (ξ {F = (L :=□) v} M→M′)
        (done w) →
          case canonical-ref ⊢L v of λ where
            (Ref-addr eq _) →
              let ⟨ T , ℓ , _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ eq in
                step (assign w eq)
            (Ref-proxy r i _) → step (assign-cast (ref-is-value r) w i)
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
progress (cast-pc ℓ M) (⊢cast-pc ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→N) → step (ξ {F = cast-pc ℓ □} M→N)
    (done v) → step (β-cast-pc v)
    (err E-error) → step (ξ-err {F = cast-pc ℓ □})
progress (error e) ⊢err μ ⊢μ pc = err E-error
progress M (⊢sub ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc
progress M (⊢sub-pc ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc


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
relax-Σ (⊢nsu-ref ⊢M) Σ′⊇Σ = ⊢nsu-ref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢nsu-assign ⊢L ⊢M) Σ′⊇Σ = ⊢nsu-assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢prot ⊢M) Σ′⊇Σ = ⊢prot (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢cast-pc ⊢M) Σ′⊇Σ = ⊢cast-pc (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ ⊢err Σ′⊇Σ = ⊢err
relax-Σ (⊢sub ⊢M A<:B) Σ′⊇Σ = ⊢sub (relax-Σ ⊢M Σ′⊇Σ) A<:B
relax-Σ (⊢sub-pc ⊢M gc<:gc′) Σ′⊇Σ = ⊢sub-pc (relax-Σ ⊢M Σ′⊇Σ) gc<:gc′

plug-inversion : ∀ {Σ gc M A} {F : Frame}
  → [] ; Σ ; gc ⊢ plug M F ⦂ A
    -------------------------------------------------------------
  → ∃[ gc′ ] ∃[ B ]
       ([] ; Σ ; gc′ ⊢ M ⦂ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc′ ⊢ M′ ⦂ B → Σ′ ⊇ Σ → [] ; Σ′ ; gc ⊢ plug M′ F ⦂ A)
plug-inversion {F = □· M} (⊢app ⊢L ⊢M) =
  ⟨ _ , _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V ·□) v} (⊢app ⊢V ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = ref[ ℓ ]□} (⊢ref ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref ⊢M′) ⟩
plug-inversion {F = !□} (⊢deref ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′) ⟩
plug-inversion {F = □:= M} (⊢assign ⊢L ⊢M) =
  ⟨ _ , _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V :=□) v} (⊢assign ⊢V ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = let□ N} (⊢let ⊢M ⊢N) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = if□ M N} (⊢if ⊢L ⊢M ⊢N) =
  ⟨ _ , _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = □⟨ c ⟩} (⊢cast ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩
plug-inversion {F = nsu-assign□ M} (⊢nsu-assign ⊢L ⊢M) =
  ⟨ _ , _ , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢nsu-assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = cast-pc ℓ □} (⊢cast-pc ⊢M) =
  ⟨ _ , _ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast-pc ⊢M′) ⟩
plug-inversion (⊢sub ⊢M A<:B) =
  let ⟨ gc′ , B , ⊢M , wt-plug ⟩ = plug-inversion ⊢M in
    ⟨ gc′ , B , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub (wt-plug ⊢M′ Σ′⊇Σ) A<:B) ⟩
plug-inversion (⊢sub-pc ⊢plug gc<:gc′) =
  let ⟨ gc″ , B , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug in
    ⟨ gc″ , B , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub-pc (wt-plug ⊢M′ Σ′⊇Σ) gc<:gc′) ⟩

preserve : ∀ {Σ gc M M′ A μ μ′ pc}
  → [] ; Σ ; gc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → M ∣ μ ∣ pc —→ M′ ∣ μ′
    ----------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
preserve ⊢plug ⊢μ pc≾gc (ξ {F = F} M→M′) =
  let ⟨ gc′ , B , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug
      ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = preserve ⊢M ⊢μ {!!} M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , wt-plug ⊢M′ Σ′⊇Σ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ pc≾gc ξ-err = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢prot ⊢V) ⊢μ pc≾gc (prot-val v) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢value-gc (stamp-val-wt ⊢V v) (stamp-val-value v) , ⊢μ ⟩
preserve (⊢prot ⊢M) ⊢μ pc≾gc (prot-ctx M→M′) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ {!!} M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢prot ⊢M′ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ pc≾gc prot-err = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve (⊢app ⊢V ⊢M) ⊢μ pc≾gc (β v) = {!!}
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (β-if-true {ℓ = ℓ}) =
  case const-label-≼ ⊢L of λ where
    ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
      let gc⋎ℓ<:gc⋎ℓ′ = consis-join-<:ₗ <:ₗ-refl (<:-l ℓ≼ℓ′)
          A⋎ℓ<:A⋎ℓ′   = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
        ⟨ Σ , ⊇-refl {Σ} , ⊢sub (⊢prot (⊢sub-pc ⊢M gc⋎ℓ<:gc⋎ℓ′)) A⋎ℓ<:A⋎ℓ′ , ⊢μ ⟩
preserve {Σ} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (β-if-false {ℓ = ℓ}) =
  case const-label-≼ ⊢L of λ where
    ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
      let gc⋎ℓ<:gc⋎ℓ′ = consis-join-<:ₗ <:ₗ-refl (<:-l ℓ≼ℓ′)
          A⋎ℓ<:A⋎ℓ′   = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
        ⟨ Σ , ⊇-refl {Σ} , ⊢sub (⊢prot (⊢sub-pc ⊢N gc⋎ℓ<:gc⋎ℓ′)) A⋎ℓ<:A⋎ℓ′ , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (β-let x) = {!!}
preserve ⊢M ⊢μ pc≾gc (ref x x₁) = {!!}
preserve {Σ} (⊢nsu-ref ⊢M) ⊢μ pc≾gc (nsu-ref-ok pc≼ℓ) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢cast-pc ⊢M , ⊢μ ⟩
preserve {Σ} (⊢nsu-ref ⊢M) ⊢μ pc≾gc (nsu-ref-fail pc⋠ℓ) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (deref x) = {!!}
preserve ⊢M ⊢μ pc≾gc (assign x x₁) = {!!}
preserve {Σ} (⊢nsu-assign ⊢L ⊢M) ⊢μ pc≾gc (nsu-assign-ok w eq1 eq2 pc≼ℓ₁) =
  ⟨ Σ , ⊇-refl {Σ} , {!!} , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (nsu-assign-fail w x x₁ x₂) = {!!}
preserve ⊢M ⊢μ pc≾gc (cast ⊢V v a) = {!!}
preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (if-cast-true i) = {!!}
preserve ⊢M ⊢μ pc≾gc (if-cast-false x) = {!!}
preserve {Σ} {gc} (⊢app ⊢Vc ⊢W) ⊢μ pc≾gc (fun-cast {V} {W} {pc = pc} v w i) with i
... | (I-fun (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ l pc₂ ] C ⇒ D of g₂) p c~) I-label I-label) =
  case ⟨ canonical-fun ⊢Vc (V-cast v i) , c~ ⟩ of λ where
    ⟨ Fun-proxy f _ (<:-ty g₂<:g (<:-fun gc⋎g<:pc₂ A₁<:C D<:B₁)) , ~-ty g₁~g₂ (~-fun l~ _ _) ⟩ →
      -- doing some label arithmetic ...
      case ⟨ g₁~g₂ , g₂<:g , consis-join-<:ₗ-inv gc⋎g<:pc₂ ⟩ of λ where
        ⟨ l~ , <:-l g₂≼g , <:-l gc≼pc₂ , <:-l g≼pc₂ ⟩ →
          let ⊢V = fun-wt {gc = gc} f
              g₂≼pc₂ = ≼-trans g₂≼g g≼pc₂
              gc⋎g₂≼pc₂ = subst (λ □ → _ ⋎ _ ≼ □) ℓ⋎ℓ≡ℓ (join-≼′ gc≼pc₂ g₂≼pc₂)
              ⊢V† = ⊢sub ⊢V (<:-ty <:ₗ-refl (<:-fun (<:-l gc⋎g₂≼pc₂) <:-refl <:-refl)) in
          ⟨ Σ , ⊇-refl {Σ} ,
            ⊢sub (⊢cast (⊢app ⊢V† (⊢cast (⊢sub (⊢value-gc ⊢W w) A₁<:C)))) (stamp-<: D<:B₁ g₂<:g) , ⊢μ ⟩
... | (I-fun (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ ⋆ ] C ⇒ D of g₂) p c~) I-label I-label)
  with (pc ⋎ ℓ₁) ≼? pc₁
... | (yes pc⋎ℓ₁≼pc₁) =
  case ⟨ canonical-fun ⊢Vc (V-cast v i) , c~ ⟩ of λ where
    ⟨ Fun-proxy f _ (<:-ty g₂<:g (<:-fun gc⋎g<:⋆ A₁<:C D<:B₁)) , ~-ty g₁~g₂ (~-fun ~⋆ _ _) ⟩ →
      let ⊢V = fun-wt {gc = gc} f
          ⊢V† = ⊢value-gc {gc′ = l pc} (⊢sub ⊢V (<:-ty <:ₗ-refl (<:-fun (<:-l pc⋎ℓ₁≼pc₁) <:-refl <:-refl))) v in
      ⟨ Σ , ⊇-refl {Σ} ,
            ⊢sub (⊢cast (⊢cast-pc (⊢app ⊢V† (⊢cast (⊢sub (⊢value-gc ⊢W w) A₁<:C))))) (stamp-<: D<:B₁ g₂<:g) , ⊢μ ⟩
... | (no  pc⋎ℓ₁⋠pc₁) = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (deref-cast x x₁) = {!!}
preserve ⊢M ⊢μ pc≾gc (assign-cast x x₁ x₂) = {!!}
preserve {Σ} (⊢cast-pc ⊢V) ⊢μ pc≾gc (β-cast-pc v) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢value-gc ⊢V v , ⊢μ ⟩
preserve (⊢sub ⊢M A<:B) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≾gc M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢M′ A<:B , ⊢μ′ ⟩
preserve (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub-pc ⊢M′ gc<:gc′ , ⊢μ′ ⟩
