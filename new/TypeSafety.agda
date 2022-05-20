open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
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

progress : ∀ {Σ gc pc A} M → [] ; Σ ; gc ; pc ⊢ M ⦂ A → ∀ μ → Σ ⊢ μ → ∀ pc → Progress M μ pc
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
progress (if L A M N) (⊢if {g = g} ⊢L ⊢M ⊢N) μ ⊢μ pc =
  case progress L ⊢L μ ⊢μ pc of λ where
    (step L→L′) → step (ξ {F = if□ A M N} L→L′)
    (done v) →
      case canonical-const ⊢L v of λ where
        (Const-base {𝔹} {true} _)   → step β-if-true
        (Const-base {𝔹} {false} _)  → step β-if-false
        (Const-inj {𝔹} {true} _)  → step (if-cast-true (I-base-inj _))
        (Const-inj {𝔹} {false} _) → step (if-cast-false (I-base-inj _))
    (err (E-error {e})) → step (ξ-err {F = if□ A M N} {e = e})
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
          let ⟨ _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ eq in
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
              let ⟨ _ , V₁ , eq , ⊢V₁ ⟩ = ⊢μ _ eq in
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
      let ⟨ a , ℓ , eq₁ , A′ , ⊢a ⟩ = unwrap-ref ⊢L v
          ⟨ T , ℓ₁ , A≡Tℓ₁ , eq ⟩   = ⊢addr-inv ⊢a
          ⟨ _ , V₁ , eq₂ , ⊢V₁ ⟩    = ⊢μ _ eq in
        case pc ≼? ℓ₁ of λ where
          (yes pc≼ℓ₁) → step (nsu-assign-ok v eq₁ eq₂ pc≼ℓ₁)
          (no  pc⋠ℓ₁) → step (nsu-assign-fail v eq₁ eq₂ pc⋠ℓ₁)
    (err (E-error {e})) → step (ξ-err {F = nsu-assign□ M} {e = e})
progress (prot[ ℓ ] M) (⊢prot ⊢M) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ (pc ⋎ ℓ) of λ where
    (step M→N) → step (prot-ctx M→N)
    (done v) → step (prot-val v)
    (err E-error) → step prot-err
progress (cast-pc g M) (⊢cast-pc ⊢M pc≾g) μ ⊢μ pc =
  case progress M ⊢M μ ⊢μ pc of λ where
    (step M→N) → step (ξ {F = cast-pc g □} M→N)
    (done v) → step (β-cast-pc v)
    (err E-error) → step (ξ-err {F = cast-pc g □})
progress (error e) ⊢err μ ⊢μ pc = err E-error
progress M (⊢sub ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc
progress M (⊢sub-pc ⊢M _) μ ⊢μ pc = progress M ⊢M μ ⊢μ pc


plug-inversion : ∀ {Σ gc pc M A} {F : Frame}
  → [] ; Σ ; gc ; pc ⊢ plug M F ⦂ A
  → l pc ≾ gc
    -------------------------------------------------------------
  → ∃[ gc′ ] ∃[ B ]
       (l pc ≾ gc′) × ([] ; Σ ; gc′ ; pc ⊢ M ⦂ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc′ ; pc ⊢ M′ ⦂ B → Σ′ ⊇ Σ → [] ; Σ′ ; gc ; pc ⊢ plug M′ F ⦂ A)
plug-inversion {F = □· M} (⊢app ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V ·□) v} (⊢app ⊢V ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = ref[ ℓ ]□} (⊢ref ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref ⊢M′) ⟩
plug-inversion {F = !□} (⊢deref ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′) ⟩
plug-inversion {F = □:= M} (⊢assign ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V :=□) v} (⊢assign ⊢V ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = let□ N} (⊢let ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = if□ A M N} (⊢if ⊢L ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = □⟨ c ⟩} (⊢cast ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩
plug-inversion {F = nsu-assign□ M} (⊢nsu-assign ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢nsu-assign ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = cast-pc g □} (⊢cast-pc ⊢M pc≾g) _ =
  ⟨ g , _ , pc≾g , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast-pc ⊢M′ pc≾g) ⟩
plug-inversion (⊢sub ⊢M A<:B) pc≾gc =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢M pc≾gc in
    ⟨ gc′ , B , pc≾gc′ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub (wt-plug ⊢M′ Σ′⊇Σ) A<:B) ⟩
plug-inversion (⊢sub-pc ⊢plug gc<:gc′) pc≾gc =
  let ⟨ gc″ , B , pc≾gc″ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug (≾-<: pc≾gc gc<:gc′) in
    ⟨ gc″ , B , pc≾gc″ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub-pc (wt-plug ⊢M′ Σ′⊇Σ) gc<:gc′) ⟩

preserve : ∀ {Σ gc pc M M′ A μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → M ∣ μ ∣ pc —→ M′ ∣ μ′
    ----------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ M′ ⦂ A) × (Σ′ ⊢ μ′)
preserve ⊢plug ⊢μ pc≾gc (ξ {F = F} M→M′) =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug pc≾gc
      ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩  = preserve ⊢M ⊢μ pc≾gc′ M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , wt-plug ⊢M′ Σ′⊇Σ , ⊢μ′ ⟩
preserve {Σ} ⊢M ⊢μ pc≾gc ξ-err = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve {Σ} (⊢prot ⊢V) ⊢μ pc≾gc (prot-val v) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢value-pc (stamp-val-wt ⊢V v) (stamp-val-value v) , ⊢μ ⟩
preserve (⊢prot ⊢M) ⊢μ pc≾gc (prot-ctx M→M′) =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (consis-join-≾ pc≾gc ≾-refl) M→M′ in
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
preserve {Σ} {μ = μ} (⊢ref {T = T} {ℓ} ⊢V) ⊢μ pc≾gc (ref {a = a} v fresh {- `a` is fresh -}) =
  let is-here = here {Addr} {RawType × StaticLabel} {_≟_} {a} in
  ⟨ ⟨ a , T , ℓ ⟩ ∷ Σ , ⊇-fresh {μ = μ} ⊢μ fresh , ⊢addr is-here , ⊢μ-ext (⊢value-pc ⊢V v) ⊢μ fresh ⟩
preserve {Σ} (⊢nsu-ref ⊢M) ⊢μ pc≾gc (nsu-ref-ok pc≼ℓ) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢cast-pc ⊢M (≾-l pc≼ℓ) , ⊢μ ⟩
preserve {Σ} (⊢nsu-ref ⊢M) ⊢μ pc≾gc (nsu-ref-fail pc⋠ℓ) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (deref x) = {!!}
preserve ⊢M ⊢μ pc≾gc (assign x x₁) = {!!}
preserve {Σ} (⊢nsu-assign ⊢L ⊢M) ⊢μ pc≾gc (nsu-assign-ok w eq1 eq2 pc≼ℓ₁) =
  ⟨ Σ , ⊇-refl {Σ} , {!!} , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (nsu-assign-fail w x x₁ x₂) = {!!}
preserve ⊢M ⊢μ pc≾gc (cast ⊢V v a) = {!!}
preserve {Σ} {gc} {pc} (⊢if {A = A} {L} {M} {N} ⊢L ⊢M ⊢N) ⊢μ pc≾gc (if-cast-true i) with i
... | (I-base-inj (cast (` Bool of l ℓ′) (` Bool of ⋆) p _)) =
  case canonical-const ⊢L (V-cast V-const i) of λ where
    (Const-inj {ℓ = ℓ} ℓ≼ℓ′) →
      let ⊢M† : [] ; Σ ; ⋆ ; pc ⋎ ℓ ⊢ M ⦂ A
          ⊢M† = subst (λ □ → [] ; Σ ; □ ; pc ⋎ ℓ ⊢ M ⦂ A) g⋎̃⋆≡⋆ (⊢M {pc ⋎ ℓ}) in
      ⟨ Σ , ⊇-refl {Σ} , ⊢cast (⊢prot (⊢cast-pc ⊢M† ≾-⋆r)) , ⊢μ ⟩
preserve {Σ} {gc} {pc} (⊢if {A = A} {L} {M} {N} ⊢L ⊢M ⊢N) ⊢μ pc≾gc (if-cast-false i) with i
... | (I-base-inj (cast (` Bool of l ℓ′) (` Bool of ⋆) p _)) =
  case canonical-const ⊢L (V-cast V-const i) of λ where
    (Const-inj {ℓ = ℓ} ℓ≼ℓ′) →
      let ⊢N† : [] ; Σ ; ⋆ ; pc ⋎ ℓ ⊢ N ⦂ A
          ⊢N† = subst (λ □ → [] ; Σ ; □ ; pc ⋎ ℓ ⊢ N ⦂ A) g⋎̃⋆≡⋆ (⊢N {pc ⋎ ℓ}) in
      ⟨ Σ , ⊇-refl {Σ} , ⊢cast (⊢prot (⊢cast-pc ⊢N† ≾-⋆r)) , ⊢μ ⟩
preserve {Σ} {gc} {pc} (⊢app ⊢Vc ⊢W) ⊢μ pc≾gc (fun-cast {V} {W} {pc = pc} v w i) with i
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
            ⊢sub (⊢cast (⊢app ⊢V† (⊢cast (⊢sub (⊢value-pc ⊢W w) A₁<:C)))) (stamp-<: D<:B₁ g₂<:g) , ⊢μ ⟩
... | (I-fun (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ ⋆ ] C ⇒ D of g₂) p c~) I-label I-label)
  with (pc ⋎ ℓ₁) ≼? pc₁
... | (yes pc⋎ℓ₁≼pc₁) =
  case ⟨ canonical-fun ⊢Vc (V-cast v i) , c~ ⟩ of λ where
    ⟨ Fun-proxy f _ (<:-ty g₂<:g (<:-fun gc⋎g<:⋆ A₁<:C D<:B₁)) , ~-ty g₁~g₂ (~-fun ~⋆ _ _) ⟩ →
      let ⊢V = fun-wt {gc = gc} {pc = pc} f
          ⊢V† = ⊢value-pc {gc′ = l pc} (⊢sub ⊢V (<:-ty <:ₗ-refl (<:-fun (<:-l pc⋎ℓ₁≼pc₁) <:-refl <:-refl))) v in
      ⟨ Σ , ⊇-refl {Σ} ,
            ⊢sub (⊢cast (⊢cast-pc (⊢app ⊢V† (⊢cast (⊢sub (⊢value-pc ⊢W w) A₁<:C))) ≾-refl)) (stamp-<: D<:B₁ g₂<:g) , ⊢μ ⟩
... | (no  pc⋎ℓ₁⋠pc₁) = ⟨ Σ , ⊇-refl {Σ} , ⊢err , ⊢μ ⟩
preserve ⊢M ⊢μ pc≾gc (deref-cast x x₁) = {!!}
preserve ⊢M ⊢μ pc≾gc (assign-cast x x₁ x₂) = {!!}
preserve {Σ} (⊢cast-pc ⊢V _) ⊢μ pc≾gc (β-cast-pc v) =
  ⟨ Σ , ⊇-refl {Σ} , ⊢value-pc ⊢V v , ⊢μ ⟩
preserve (⊢sub ⊢M A<:B) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ pc≾gc M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢M′ A<:B , ⊢μ′ ⟩
preserve (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M→M′ =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢M′ , ⊢μ′ ⟩ = preserve ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M→M′ in
    ⟨ Σ′ , Σ′⊇Σ , ⊢sub-pc ⊢M′ gc<:gc′ , ⊢μ′ ⟩
