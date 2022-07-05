module RelatedHeaps where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Reduction
open import Utils

open import Erasure


{- Related heaps -}
_≈_ : ∀ (μ μ′ : Heap) → Set
μ ≈ μ′ = ≈-left × ≈-right
  where
  ≈-left  = ∀ a {V} → key _≟_ μ a ≡ just ⟨ V , low ⟩
                    → ∃[ V′ ] (key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩) × (V′ ≡ erase V)
  ≈-right = ∀ a {V′} → key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩
                    → ∃[ V ] (key _≟_ μ a ≡ just ⟨ V , low ⟩) × (V′ ≡ erase V)

_≋_ : ∀ (μ μ′ : Heap) → Set
μ ≋ μ′ = ≋-left × ≋-right
  where
  ≋-left  = ∀ a {V}  → key _≟_ μ a  ≡ just ⟨ V , low ⟩
                     → ∃[ V′ ] (key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩) × (V′ ≡ V)
  ≋-right = ∀ a {V′} → key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩
                     → ∃[ V ]  (key _≟_ μ a ≡ just ⟨ V , low ⟩) × (V′ ≡ V)

≋-refl : ∀ μ → μ ≋ μ
≋-refl μ = ⟨ (λ a eq → ⟨ _ , eq , refl ⟩) , (λ a eq → ⟨ _ , eq , refl ⟩) ⟩

postulate
  ref-erase-inv : ∀ {N′ ℓ} M
    → ref✓[ ℓ ] N′ ≡ erase M
    → ∃[ N ] (M ≡ ref✓[ ℓ ] N) × (N′ ≡ erase N)
-- erase-ref-inv {addr _ of _} ()
-- erase-ref-inv {ref✓[ ℓ ] N} refl = ⟨ N , refl , refl ⟩

ref✓-wt-inv : ∀ {Γ Σ gc pc A M ℓ}
  → Γ ; Σ ; gc ; pc ⊢ ref✓[ ℓ ] M ⦂ A
  → pc ≼ ℓ
ref✓-wt-inv (⊢ref✓ _ pc≼ℓ)      = pc≼ℓ
ref✓-wt-inv (⊢sub ⊢M A<:B)       = ref✓-wt-inv ⊢M
ref✓-wt-inv (⊢sub-pc ⊢M gc<:gc′) = ref✓-wt-inv ⊢M

-- μ≋-update : ∀ {μ a V} → μ ≋ (⟨ a , V , high ⟩ ∷ μ)
-- μ≋-update {μ} {a₁} {V₁} = ?

high-pc-≋ : ∀ {Σ gc A M M₁ M₂ μ₁ μ₂}
  → M₁ ∣ μ₁ ∣ Σ ∣ high —→ M₂ ∣ μ₂
  → [] ; Σ ; gc ; high ⊢ M ⦂ A
  → M₁ ≡ erase M
    ---------------------
  → μ₁ ≋ μ₂
high-pc-≋ (ξ M₁→M₂) ⊢M eq = {!!}
high-pc-≋ ξ-err ⊢M eq = {!!}
high-pc-≋ (prot-val v) ⊢M eq = {!!}
high-pc-≋ (prot-ctx R) ⊢M eq = {!!}
high-pc-≋ prot-err ⊢M eq = {!!}
high-pc-≋ {μ₁ = μ₁} (β v) ⊢M eq = ≋-refl μ₁
high-pc-≋ β-if-true ⊢M eq = {!!}
high-pc-≋ β-if-false ⊢M eq = {!!}
high-pc-≋ (β-let x) ⊢M eq = {!!}
high-pc-≋ ref-static ⊢M eq = {!!}
high-pc-≋ (ref?-ok x) ⊢M eq = {!!}
high-pc-≋ (ref?-fail x) ⊢M eq = {!!}
high-pc-≋ {M = M} (ref v fresh) ⊢M eq
  with ref-erase-inv M eq
... | ⟨ N , eq₁ , refl ⟩ rewrite eq₁ =
  case ref✓-wt-inv ⊢M {- high ≼ ℓ -} of λ where
  h⊑h → {!!}
high-pc-≋ (deref x) ⊢M eq = {!!}
high-pc-≋ assign-static ⊢M eq = {!!}
high-pc-≋ (assign?-ok x x₁) ⊢M eq = {!!}
high-pc-≋ (assign?-fail x x₁) ⊢M eq = {!!}
high-pc-≋ (assign x x₁) ⊢M eq = {!!}
high-pc-≋ (cast ⊢V v a) ⊢M eq = {!!}
high-pc-≋ (if-cast-true x) ⊢M eq = {!!}
high-pc-≋ (if-cast-false x) ⊢M eq = {!!}
high-pc-≋ (fun-cast x x₁ i) ⊢M eq = {!!}
high-pc-≋ (deref-cast x x₁) ⊢M eq = {!!}
high-pc-≋ (assign?-cast x i) ⊢M eq = {!!}
high-pc-≋ (assign-cast x x₁ i) ⊢M eq = {!!}
high-pc-≋ (β-cast-pc x) ⊢M eq = {!!}
high-pc-≋ (app-● x) ⊢M eq = {!!}
high-pc-≋ if-● ⊢M eq = {!!}
high-pc-≋ deref-● ⊢M eq = {!!}
high-pc-≋ {μ₁ = μ₁} (assign-● x) ⊢M eq = ≋-refl μ₁
