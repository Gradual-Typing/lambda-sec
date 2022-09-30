{- TODO -}
{-# OPTIONS --allow-unsolved-metas #-}

module BigStepPreservation where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import BigStep

open import WellTyped public
open import Preservation public


⇓-preserve : ∀ {Σ gc pc M V A μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ---------------------------------------------------------------
  → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ V ⦂ A) × (Σ′ ⊢ μ′)
⇓-preserve {Σ} {μ = μ} ⊢V ⊢μ pc≾gc (⇓-val v) = ⟨ Σ , ⊇-refl Σ , ⊢V , ⊢μ ⟩
⇓-preserve (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app L⇓ƛN M⇓V N[V]⇓W) =
  let v = ⇓-value M⇓V
      w = ⇓-value N[V]⇓W in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢ƛN , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-fun ⊢ƛN V-ƛ of λ where
  (Fun-ƛ ⊢N (<:-ty ℓ<:g (<:-fun gc⋎g<:gc′ A<:A′ B′<:B))) →
    let gc⋎ℓ<:gc⋎g = consis-join-<:ₗ <:ₗ-refl ℓ<:g
        gc⋎ℓ<:gc′  = <:ₗ-trans gc⋎ℓ<:gc⋎g gc⋎g<:gc′
        pc⋎ℓ≾gc′   = ≾-<: (consis-join-≾ pc≾gc ≾-refl) gc⋎ℓ<:gc′ in
    let ⊢N[V] = substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁) (⊢value-pc (⊢sub ⊢V A<:A′) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢N[V] ⊢μ₂ pc⋎ℓ≾gc′ N[V]⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) ,
      (⊢sub (stamp-val-wt (⊢value-pc ⊢W w) w) (stamp-<: B′<:B ℓ<:g)) , ⊢μ₃ ⟩
⇓-preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-true L⇓true M⇓V) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢true , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true in
  case const-label-≼ ⊢true of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    let pc⋎ℓ≾gc⋎ℓ′ = consis-join-≾ pc≾gc (≾-l ℓ≼ℓ′) in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎ℓ′ M⇓V in
    let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ ,
      ⊢sub (stamp-val-wt (⊢value-pc ⊢V v) v) A⋎ℓ<:A⋎ℓ′ , ⊢μ₂ ⟩
⇓-preserve (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-false L⇓false N⇓V) =
  let v = ⇓-value N⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢false , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false in
  case const-label-≼ ⊢false of λ where
  ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ →
    let pc⋎ℓ≾gc⋎ℓ′ = consis-join-≾ pc≾gc (≾-l ℓ≼ℓ′) in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎ℓ′ N⇓V in
    let A⋎ℓ<:A⋎ℓ′ = stamp-<: <:-refl (<:-l ℓ≼ℓ′) in
    ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ ,
      ⊢sub (stamp-val-wt (⊢value-pc ⊢V v) v) A⋎ℓ<:A⋎ℓ′ , ⊢μ₂ ⟩
⇓-preserve (⊢let ⊢M ⊢N) ⊢μ pc≾gc (⇓-let M⇓V N[V]⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  let ⊢N[V] = substitution-pres (relax-Σ ⊢N Σ₁⊇Σ) (⊢value-pc ⊢V v) in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢W , ⊢μ₂ ⟩ = ⇓-preserve ⊢N[V] ⊢μ₁ pc≾gc N[V]⇓W in
  ⟨ Σ₂ , ⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ , ⊢W , ⊢μ₂ ⟩
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-ref? M⇓V x x₁) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-ref M⇓V x) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-deref M⇓V x) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-assign? M⇓V M⇓V₁ x) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-assign M⇓V M⇓V₁) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-cast x M⇓V x₁ M⇓V₁) = {!!}
⇓-preserve {gc = gc} {pc} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-true {ℓ = ℓ} i L⇓true⟨c⟩ M⇓V V⋎ℓ⟨bc⟩⇓W) =
  let v = ⇓-value M⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢true⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true⟨c⟩ in
  case canonical-const ⊢true⟨c⟩ (⇓-value L⇓true⟨c⟩) of λ where
  (Const-inj _) →  {- g = ⋆ -}
    let pc⋎ℓ≾gc⋎g : l (pc ⋎ ℓ) ≾ (gc ⋎̃ ⋆)
        pc⋎ℓ≾gc⋎g = subst (λ □ → _ ≾ □) (sym (g⋎̃⋆≡⋆ {gc})) ≾-⋆r in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎g M⇓V in
    let ⊢V⋎ℓ⟨bc⟩ = ⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢V⋎ℓ⟨bc⟩ ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) , ⊢W , ⊢μ₃ ⟩
⇓-preserve {gc = gc} {pc} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc (⇓-if-cast-false {ℓ = ℓ} i L⇓false⟨c⟩ N⇓V V⋎ℓ⟨bc⟩⇓W) =
  let v = ⇓-value N⇓V in
  let ⟨ Σ₁ , Σ₁⊇Σ , ⊢false⟨c⟩ , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false⟨c⟩ in
  case canonical-const ⊢false⟨c⟩ (⇓-value L⇓false⟨c⟩) of λ where
  (Const-inj _) →  {- g = ⋆ -}
    let pc⋎ℓ≾gc⋎g : l (pc ⋎ ℓ) ≾ (gc ⋎̃ ⋆)
        pc⋎ℓ≾gc⋎g = subst (λ □ → _ ≾ □) (sym (g⋎̃⋆≡⋆ {gc})) ≾-⋆r in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ pc⋎ℓ≾gc⋎g N⇓V in
    let ⊢V⋎ℓ⟨bc⟩ = ⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v) in
    let ⟨ Σ₃ , Σ₃⊇Σ₂ , ⊢W , ⊢μ₃ ⟩ = ⇓-preserve ⊢V⋎ℓ⟨bc⟩ ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W in
    ⟨ Σ₃ , ⊇-trans Σ₃⊇Σ₂ (⊇-trans Σ₂⊇Σ₁ Σ₁⊇Σ) , ⊢W , ⊢μ₃ ⟩
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-fun-cast i M⇓V M⇓V₁ M⇓V₂) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-deref-cast x M⇓V M⇓V₁) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-assign?-cast i M⇓V M⇓V₁) = {!!}
⇓-preserve ⊢M ⊢μ pc≾gc (⇓-assign-cast i M⇓V M⇓V₁) = {!!}
⇓-preserve (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢V , ⊢μ′ ⟩ = ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub ⊢V A<:B , ⊢μ′ ⟩
⇓-preserve (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V =
  let ⟨ Σ′ , Σ′⊇Σ , ⊢V , ⊢μ′ ⟩ = ⇓-preserve ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V in
  ⟨ Σ′ , Σ′⊇Σ , ⊢sub-pc ⊢V gc<:gc′ , ⊢μ′ ⟩
