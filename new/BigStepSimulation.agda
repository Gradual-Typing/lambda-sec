module BigStepSimulation where

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
open import BigStepErased
open import Erasure

postulate
  erase-substitution : ∀ N M → erase (N [ M ]) ≡ erase N [ erase M ]

{- replace this with `TypeSafety` in future -}
open import Preservation
postulate
  ⇓-preserve : ∀ {Σ gc pc M V A μ μ′}
    → [] ; Σ ; gc ; pc ⊢ M ⦂ A
    → Σ ⊢ μ
    → l pc ≾ gc
    → μ ∣ pc ⊢ M ⇓ V ∣ μ′
      ---------------------------------------------------------------
    → ∃[ Σ′ ] (Σ′ ⊇ Σ) × ([] ; Σ′ ; gc ; pc ⊢ V ⦂ A) × (Σ′ ⊢ μ′)

sim : ∀ {Σ gc pc A M V μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
sim ⊢M (⇓-val v) = (⇓ₑ-val (erase-val-value v))
sim {pc = pc} (⊢app ⊢L ⊢M) (⇓-app {L = L} {M} {N} {V} {W} {ℓ = low} L⇓ƛN M⇓V N[V]⇓W)
  rewrite stamp-val-low (⇓-value N[V]⇓W)
  rewrite ℓ⋎low≡ℓ {pc} =
  ⇓ₑ-app (sim ⊢L L⇓ƛN) (sim ⊢M M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (erase-substitution N V) =
    let ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩ = ⇓-preserve ⊢L {!!} {!!} L⇓ƛN in
    let ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ = ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ {!!} M⇓V in
    case canonical-fun ⊢ƛN V-ƛ of λ where
    (Fun-ƛ ⊢N (<:-ty _ (<:-fun _ A₁<:A _))) →
      sim (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁) (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V))) N[V]⇓W
  {- need to prove preservation -}
sim {pc = pc} (⊢app {L = L} {M} ⊢L ⊢M) (⇓-app {ℓ = high} L⇓ƛN M⇓V N[V]⇓W)
  rewrite erase-stamp-high (⇓-value N[V]⇓W) =
  let ϵL⇓● = sim ⊢L L⇓ƛN in
  let ϵM⇓ϵV = sim ⊢M M⇓V  in
  ϵL·ϵM⇓●
  where
  ϵL·ϵM⇓● : _ ∣ pc ⊢ erase L · erase M ⇓ₑ ● ∣ _
  ϵL·ϵM⇓● = ⇓ₑ-app-● (sim ⊢L L⇓ƛN) {!!}
  {- in this case we need to show if μ ∣ high ⊢ M ⇓ V ∣ μ′ then ϵ(μ) ≡ ϵ(μ′) -}
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
sim (⊢sub ⊢M A<:B) M⇓V = sim ⊢M M⇓V
sim (⊢sub-pc ⊢M gc<:gc′) M⇓V = sim ⊢M M⇓V

