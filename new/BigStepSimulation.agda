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

open import BigStepPreservation
open import HeapSecure

postulate
  erase-substitution : ∀ N M → erase (N [ M ]) ≡ erase N [ erase M ]

sim : ∀ {Σ gc pc A M V μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ ⊢ μ
  → l pc ≾ gc
  → μ ∣ pc ⊢ M ⇓ V ∣ μ′
    ----------------------------------------------------------------------------------
  → erase-μ μ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
sim ⊢M ⊢μ pc≾gc (⇓-val v) = (⇓ₑ-val (erase-val-value v))
sim {pc = pc} (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app {L = L} {M} {N} {V} {W} {ℓ = low} L⇓ƛN M⇓V N[V]⇓W)
  rewrite stamp-val-low (⇓-value N[V]⇓W)
  rewrite ℓ⋎low≡ℓ {pc}
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩ =
  ⇓ₑ-app (sim ⊢L ⊢μ pc≾gc L⇓ƛN) (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (erase-substitution N V) =
    case canonical-fun ⊢ƛN V-ƛ of λ where
    (Fun-ƛ ⊢N (<:-ty _ (<:-fun gc⋎g<:pc′ A₁<:A _))) →
      case ⟨ pc≾gc , consis-join-<:ₗ-inv gc⋎g<:pc′ ⟩ of λ where
      ⟨ ≾-l pc≼gc , <:-l gc≼pc′ , _ ⟩ →
        sim (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                               (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V)))
            ⊢μ₂ (≾-l (≼-trans pc≼gc gc≼pc′)) N[V]⇓W
sim {pc = pc} {μ′ = μ′} (⊢app ⊢L ⊢M) ⊢μ pc≾gc (⇓-app {L = L} {M} {N} {V} {W} {ℓ = high} L⇓ƛN M⇓V N[V]⇓W)
  rewrite erase-stamp-high (⇓-value N[V]⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢ƛN , ⊢μ₁ ⟩
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩
  rewrite ℓ⋎high≡high {pc} =
  ⇓ₑ-app-● (sim ⊢L ⊢μ pc≾gc L⇓ƛN) ϵM⇓ϵV
  where
  ϵμ₂≡ϵμ′ =
    case canonical-fun ⊢ƛN V-ƛ of λ where
    (Fun-ƛ ⊢N (<:-ty (<:-l h≼h) (<:-fun gc⋎g<:pc′ A₁<:A _))) →
      case consis-join-<:ₗ-inv gc⋎g<:pc′ of λ where
      ⟨ <:-l gc≼pc′ , <:-l h≼h ⟩ →
        heap-relate (substitution-pres (relax-Σ ⊢N Σ₂⊇Σ₁)
                    (⊢value-pc (⊢sub ⊢V A₁<:A) (⇓-value M⇓V))) ⊢μ₂ (≾-l h≼h) N[V]⇓W
  ϵM⇓ϵV : _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ′
  ϵM⇓ϵV = subst (λ □ → _ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ □)
             ϵμ₂≡ϵμ′ (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V)
sim ⊢M ⊢μ pc≾gc (⇓-if-true M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-if-false M⇓V M⇓V₁) = {!!}
sim {pc = pc} (⊢let ⊢M ⊢N) ⊢μ pc≾gc (⇓-let {M = M} {N} {V} {W} M⇓V N[V]⇓W)
  with ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ =
  ⇓ₑ-let (sim ⊢M ⊢μ pc≾gc M⇓V) ϵN[ϵV]⇓ϵW
  where
  ϵN[ϵV]⇓ϵW : _ ∣ pc ⊢ erase N [ erase V ] ⇓ₑ erase W ∣ _
  ϵN[ϵV]⇓ϵW rewrite sym (erase-substitution N V) =
    let v = ⇓-value M⇓V in
    sim (substitution-pres (relax-Σ ⊢N Σ₁⊇Σ) (⊢value-pc ⊢V v)) ⊢μ₁ pc≾gc N[V]⇓W
sim (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? {μ} {μ₁} {ℓ = low} M⇓V fresh pc≼ℓ)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref? (sim ⊢M ⊢μ pc≾gc M⇓V) fresh pc≼ℓ
sim (⊢ref? ⊢M) ⊢μ pc≾gc (⇓-ref? {ℓ = high} M⇓V fresh pc≼ℓ) =
  ⇓ₑ-ref?-● (sim ⊢M ⊢μ pc≾gc M⇓V)
sim (⊢ref ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-ref {μ} {μ₁} {ℓ = low} M⇓V fresh)
  rewrite erase-μᴸ-length (proj₁ μ₁) =
  ⇓ₑ-ref (sim ⊢M ⊢μ pc≾gc M⇓V) fresh
sim (⊢ref ⊢M pc′≼ℓ) ⊢μ pc≾gc (⇓-ref {ℓ = high} M⇓V fresh) =
  ⇓ₑ-ref-● (sim ⊢M ⊢μ pc≾gc M⇓V)
sim {μ′ = ⟨ μᴸ , μᴴ ⟩} (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = low} {low} M⇓a eq)
  rewrite stamp-val-low v =
  ⇓ₑ-deref {v = erase-val-value v} (sim ⊢M ⊢μ pc≾gc M⇓a)
            (erase-μ-lookup-low {μᴸ} {μᴴ} {v = v} eq)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = low} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = high} {low} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim (⊢deref ⊢M) ⊢μ pc≾gc (⇓-deref {v = v} {ℓ = high} {high} M⇓a eq)
  rewrite erase-stamp-high v = ⇓ₑ-deref-● (sim ⊢M ⊢μ pc≾gc M⇓a)
sim ⊢M ⊢μ pc≾gc (⇓-assign? M⇓V M⇓V₁ x) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-assign M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-cast a M⇓V ⊢V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-if-cast-true i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-if-cast-false i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-fun-cast i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-deref-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-assign?-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-assign-cast i M⇓V M⇓V₁) = {!!}
sim (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ pc≾gc M⇓V
sim (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V

