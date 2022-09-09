module HeapSecure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import HeapTyping
open import BigStep
open import Erasure

open import BigStepPreservation

heap-relate : ∀ {Σ gc A M V μ μ′}
  → [] ; Σ ; gc ; high ⊢ M ⦂ A
  → Σ ⊢ μ
  → l high ≾ gc
  → μ ∣ high ⊢ M ⇓ V ∣ μ′
    ----------------------------------------
  → erase-μ μ ≡ erase-μ μ′
heap-relate ⊢M ⊢μ pc≾gc (⇓-val v) = refl
heap-relate (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app L⇓ƛN M⇓V N[V]⇓W) =
  let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩ = ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN in
  let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V in
  case canonical-fun ⊢ƛN V-ƛ of λ where
  (Fun-ƛ ⊢N (<:-ty _ (<:-fun gc⋎g<:pc′ A₁<:A _))) →
    case ⟨ pc≾gc , consis-join-<:ₗ-inv gc⋎g<:pc′ ⟩ of λ where
    ⟨ ≾-l h≼h , <:-l h≼h , _ ⟩ →
      let ϵμ≡ϵμ₁  = heap-relate ⊢L ⊢μ pc≾gc L⇓ƛN in
      let ϵμ₁≡ϵμ₂ = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V  in
      let ϵμ₂≡ϵμ′ = heap-relate (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                                (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V))) ⊢μ₂ pc≾gc N[V]⇓W in
      trans ϵμ≡ϵμ₁ (trans ϵμ₁≡ϵμ₂ ϵμ₂≡ϵμ′)
heap-relate ⊢M ⊢μ pc≾gc (⇓-if-true  L⇓true  M⇓V) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-if-false L⇓false N⇓V) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-let M⇓V N[V]⇓W) = {!!}
heap-relate (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? M⇓V fresh h≼h {- ℓ ≡ high -})
  rewrite heap-relate ⊢M ⊢μ pc≾gc M⇓V =
  refl
heap-relate (⊢ref ⊢M h≼h {- ℓ ≡ high -}) ⊢μ (≾-l h≼h) (⇓-ref M⇓V fresh)
  rewrite heap-relate ⊢M ⊢μ (≾-l h≼h) M⇓V =
  refl
heap-relate ⊢M ⊢μ pc≾gc (⇓-deref M⇓a eq) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-assign? L⇓a M⇓V pc≼ℓ₁) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-assign  L⇓a M⇓V) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-cast a M⇓V V⟨c⟩↝N N⇓W) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-if-cast-true  i L⇓true⟨c⟩  M⇓V V⟨bc⟩⇓W) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-if-cast-false i L⇓false⟨c⟩ N⇓V V⟨bc⟩⇓W) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-fun-cast i L⇓V⟨c⟩ M⇓W elim⇓V′) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-deref-cast   i M⇓V⟨c⟩ V⟨oc⟩⇓W) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-assign?-cast i L⇓V⟨c⟩ elim⇓W) = {!!}
heap-relate ⊢M ⊢μ pc≾gc (⇓-assign-cast  i L⇓V⟨c⟩ elim⇓W) = {!!}
heap-relate (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V = heap-relate ⊢M ⊢μ pc≾gc M⇓V
heap-relate (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V = heap-relate ⊢M ⊢μ {!!} M⇓V
