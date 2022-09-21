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
open import ApplyCastErasure

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
sim {pc = pc} {μ′ = μ′} (⊢app ⊢L ⊢M) ⊢μ pc≾gc
    (⇓-app {L = L} {M} {N} {V} {W} {ℓ = ℓ} L⇓ƛN M⇓V N[V]⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓ƛN
... | ⟨ Σ₁ , Σ₁⊇Σ  , ⊢ƛN , ⊢μ₁ ⟩
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ pc≾gc M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V  , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value N[V]⇓W) | ℓ⋎low≡ℓ {pc} =
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
...   | high
  rewrite erase-stamp-high (⇓-value N[V]⇓W) | ℓ⋎high≡high {pc} =
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
sim {pc = pc} (⊢cast ⊢M) ⊢μ pc≾gc (⇓-cast {M = M} {N} {V} {W} {c = c} a M⇓V V⟨c⟩↝N N⇓W)
  with ⇓-preserve ⊢M ⊢μ pc≾gc M⇓V
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢V , ⊢μ₁ ⟩ =
  ⇓ₑ-trans ϵM⇓ϵV ϵV⇓ϵW
  where
  ϵV≡ϵN : erase V ≡ erase N
  ϵV≡ϵN = applycast-erase V⟨c⟩↝N (error-not-⇓ N⇓W)
  v = ⇓-value M⇓V
  ϵM⇓ϵV = sim ⊢M ⊢μ pc≾gc M⇓V
  ϵN⇓ϵW = sim (applycast-pres (⊢value-pc ⊢V v) v a V⟨c⟩↝N) ⊢μ₁ pc≾gc N⇓W
  ϵV⇓ϵW : _ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ _
  ϵV⇓ϵW rewrite ϵV≡ϵN = ϵN⇓ϵW
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-cast-true {μ₁ = μ₁} {μ₂} {L = L} {M} {N} {V} {W} {A} {ℓ = ℓ} i L⇓true⟨c⟩ M⇓V V⋎ℓ⟨bc⟩⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢true⟨c⟩ , ⊢μ₁ ⟩
  with canonical-const ⊢true⟨c⟩ (⇓-value L⇓true⟨c⟩)
... | Const-inj _
  rewrite g⋎̃⋆≡⋆ {gc}
  with ⇓-preserve (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value M⇓V) =
  ⇓ₑ-if-true ϵL⇓true (⇓ₑ-trans ϵM⇓ϵV ϵV⇓ϵW)
  where
  v = ⇓-value M⇓V
  ϵL⇓true : _ ∣ pc ⊢ erase L ⇓ₑ $ true of low ∣ _
  ϵL⇓true = sim ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
  ϵM⇓ϵV : erase-μ μ₁ ∣ pc ⊢ erase M ⇓ₑ erase V ∣ erase-μ μ₂
  ϵM⇓ϵV = subst (λ □ → _ ∣ □ ⊢ _ ⇓ₑ _ ∣ _) (ℓ⋎low≡ℓ {pc})
                 (sim (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V)
  ϵV⇓ϵW : erase-μ μ₂ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ erase-μ μ′
  ϵV⇓ϵW = sim (⊢cast (⊢value-pc (subst (λ □ → [] ; _ ; _ ; _ ⊢ V ⦂ □)
              (sym (stamp-low A)) ⊢V) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
...   | high = ϵif⇓ϵW
  where
  v = ⇓-value M⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ₁
  ϵL⇓● = sim ⊢L ⊢μ pc≾gc L⇓true⟨c⟩
  ●⇓ϵW : _ ∣ pc ⊢ ● ⇓ₑ erase W ∣ _
  ●⇓ϵW rewrite sym (erase-stamp-high v) =
    sim (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
  ϵμ₁≡ϵμ₂ : erase-μ μ₁ ≡ erase-μ μ₂
  ϵμ₁≡ϵμ₂ rewrite ℓ⋎high≡high {pc} = heap-relate (relax-Σ ⊢M Σ₁⊇Σ) ⊢μ₁ ≾-⋆r M⇓V
  ϵif⇓ϵW : erase-μ μ ∣ pc ⊢ erase (if L _ M N) ⇓ₑ erase W ∣ erase-μ μ′
  ϵif⇓ϵW with V⇓ₑV ●⇓ϵW V-●
  ... | ⟨ ●≡ϵW , ϵμ₂≡ϵμ′ ⟩
    rewrite sym ●≡ϵW | sym ϵμ₂≡ϵμ′ | sym ϵμ₁≡ϵμ₂ =
    ⇓ₑ-if-● ϵL⇓●
sim {gc = gc} {pc} {μ = μ} {μ′} (⊢if ⊢L ⊢M ⊢N) ⊢μ pc≾gc
    (⇓-if-cast-false {μ₁ = μ₁} {μ₂} {L = L} {M} {N} {V} {W} {A} {ℓ = ℓ} i L⇓false⟨c⟩ N⇓V V⋎ℓ⟨bc⟩⇓W)
  with ⇓-preserve ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
... | ⟨ Σ₁ , Σ₁⊇Σ , ⊢false⟨c⟩ , ⊢μ₁ ⟩
  with canonical-const ⊢false⟨c⟩ (⇓-value L⇓false⟨c⟩)
... | Const-inj _
  rewrite g⋎̃⋆≡⋆ {gc}
  with ⇓-preserve (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V
... | ⟨ Σ₂ , Σ₂⊇Σ₁ , ⊢V , ⊢μ₂ ⟩
  with ℓ
...   | low
  rewrite stamp-val-low (⇓-value N⇓V) =
  ⇓ₑ-if-false ϵL⇓false (⇓ₑ-trans ϵN⇓ϵV ϵV⇓ϵW)
  where
  v = ⇓-value N⇓V
  ϵL⇓false : _ ∣ pc ⊢ erase L ⇓ₑ $ false of low ∣ _
  ϵL⇓false = sim ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
  ϵN⇓ϵV : erase-μ μ₁ ∣ pc ⊢ erase N ⇓ₑ erase V ∣ erase-μ μ₂
  ϵN⇓ϵV = subst (λ □ → _ ∣ □ ⊢ _ ⇓ₑ _ ∣ _) (ℓ⋎low≡ℓ {pc})
                 (sim (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V)
  ϵV⇓ϵW : erase-μ μ₂ ∣ pc ⊢ erase V ⇓ₑ erase W ∣ erase-μ μ′
  ϵV⇓ϵW = sim (⊢cast (⊢value-pc (subst (λ □ → [] ; _ ; _ ; _ ⊢ V ⦂ □)
              (sym (stamp-low A)) ⊢V) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
...   | high = ϵif⇓ϵW
  where
  v = ⇓-value N⇓V
  ϵL⇓● : erase-μ μ ∣ pc ⊢ erase L ⇓ₑ ● ∣ erase-μ μ₁
  ϵL⇓● = sim ⊢L ⊢μ pc≾gc L⇓false⟨c⟩
  ●⇓ϵW : _ ∣ pc ⊢ ● ⇓ₑ erase W ∣ _
  ●⇓ϵW rewrite sym (erase-stamp-high v) =
    sim (⊢cast (stamp-val-wt (⊢value-pc ⊢V v) v)) ⊢μ₂ pc≾gc V⋎ℓ⟨bc⟩⇓W
  ϵμ₁≡ϵμ₂ : erase-μ μ₁ ≡ erase-μ μ₂
  ϵμ₁≡ϵμ₂ rewrite ℓ⋎high≡high {pc} = heap-relate (relax-Σ ⊢N Σ₁⊇Σ) ⊢μ₁ ≾-⋆r N⇓V
  ϵif⇓ϵW : erase-μ μ ∣ pc ⊢ erase (if L _ M N) ⇓ₑ erase W ∣ erase-μ μ′
  ϵif⇓ϵW with V⇓ₑV ●⇓ϵW V-●
  ... | ⟨ ●≡ϵW , ϵμ₂≡ϵμ′ ⟩
    rewrite sym ●≡ϵW | sym ϵμ₂≡ϵμ′ | sym ϵμ₁≡ϵμ₂ =
    ⇓ₑ-if-● ϵL⇓●
sim ⊢M ⊢μ pc≾gc (⇓-fun-cast i M⇓V M⇓V₁ M⇓V₂) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-deref-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-assign?-cast i M⇓V M⇓V₁) = {!!}
sim ⊢M ⊢μ pc≾gc (⇓-assign-cast i M⇓V M⇓V₁) = {!!}
sim (⊢sub ⊢M A<:B) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ pc≾gc M⇓V
sim (⊢sub-pc ⊢M gc<:gc′) ⊢μ pc≾gc M⇓V = sim ⊢M ⊢μ (≾-<: pc≾gc gc<:gc′) M⇓V

