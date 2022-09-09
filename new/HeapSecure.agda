module HeapSecure where

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
open import BigStep
open import Erasure

heap-relate : ∀ {Σ gc pc A M V μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → μ ∣ high ⊢ M ⇓ V ∣ μ′
  → erase-μ μ ≡ erase-μ μ′
heap-relate ⊢M (⇓-val v) = refl
heap-relate ⊢M (⇓-app L⇓ƛN M⇓V N[V]⇓W) = {!!}
heap-relate ⊢M (⇓-if-true  L⇓true  M⇓V) = {!!}
heap-relate ⊢M (⇓-if-false L⇓false N⇓V) = {!!}
heap-relate ⊢M (⇓-let M⇓V N[V]⇓W) = {!!}
heap-relate ⊢M (⇓-ref? M⇓V fresh pc≼ℓ) = {!!}
heap-relate ⊢M (⇓-ref M⇓V fresh) = {!!}
heap-relate ⊢M (⇓-deref M⇓a eq) = {!!}
heap-relate ⊢M (⇓-assign? L⇓a M⇓V pc≼ℓ₁) = {!!}
heap-relate ⊢M (⇓-assign  L⇓a M⇓V) = {!!}
heap-relate ⊢M (⇓-cast a M⇓V V⟨c⟩↝N N⇓W) = {!!}
heap-relate ⊢M (⇓-if-cast-true  i L⇓true⟨c⟩  M⇓V V⟨bc⟩⇓W) = {!!}
heap-relate ⊢M (⇓-if-cast-false i L⇓false⟨c⟩ N⇓V V⟨bc⟩⇓W) = {!!}
heap-relate ⊢M (⇓-fun-cast i L⇓V⟨c⟩ M⇓W elim⇓V′) = {!!}
heap-relate ⊢M (⇓-deref-cast   i M⇓V⟨c⟩ V⟨oc⟩⇓W) = {!!}
heap-relate ⊢M (⇓-assign?-cast i L⇓V⟨c⟩ elim⇓W) = {!!}
heap-relate ⊢M (⇓-assign-cast  i L⇓V⟨c⟩ elim⇓W) = {!!}
