module BigStepSimulation where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import BigStep
open import BigStepErased
open import Erasure

sim : ∀ {Σ gc pc A M V v μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → μ ∣ Σ ∣ pc ⊢ M ⇓ V ∣ v ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ proj₁ Σ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-val-value v ∣ erase-μ μ′
sim ⊢M ⇓-val = ⇓ₑ-val
sim ⊢M (⇓-app M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M (⇓-if-true M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-if-false M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-let M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-ref? M⇓V x x₁) = {!!}
sim ⊢M (⇓-ref M⇓V x) = {!!}
sim ⊢M (⇓-deref M⇓V x) = {!!}
sim ⊢M (⇓-assign? M⇓V M⇓V₁ x) = {!!}
sim ⊢M (⇓-assign M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-cast a M⇓V ⊢V M⇓V₁) = {!!}
sim ⊢M (⇓-if-cast-true i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M (⇓-if-cast-false i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M (⇓-fun-cast i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M (⇓-deref-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-assign?-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M (⇓-assign-cast i M⇓V M⇓V₁) = {!!}
