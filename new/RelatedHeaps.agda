module RelatedHeaps where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
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
μ ≈ μ′ = ∀ a {V}
  → key _≟_ μ a ≡ just ⟨ V , low ⟩
  → ∃[ V′ ] (key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩) × (V′ ≡ erase V)

_≋_ : ∀ (μ μ′ : Heap) → Set
μ ≋ μ′ = ≋-left × ≋-right
  where
  ≋-left  = ∀ a {V}  → key _≟_ μ a  ≡ just ⟨ V , low ⟩
                     → ∃[ V′ ] (key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩) × (V′ ≡ V)
  ≋-right = ∀ a {V′} → key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩
                     → ∃[ V ]  (key _≟_ μ a ≡ just ⟨ V , low ⟩) × (V ≡ V′)

≋-refl : ∀ μ → μ ≋ μ
≋-refl μ = ⟨ (λ a eq → ⟨ _ , eq , refl ⟩) , (λ a eq → ⟨ _ , eq , refl ⟩) ⟩

high-pc-≋ : ∀ {M₁ M₂ μ₁ μ₂ Σ}
  → M₁ ∣ μ₁ ∣ Σ ∣ high —→ M₂ ∣ μ₂
  → μ₁ ≋ μ₂
-- high-pc-≋ (ξ R) = {!!}
-- high-pc-≋ ξ-err = {!!}
-- high-pc-≋ (prot-val v) = {!!}
-- high-pc-≋ (prot-ctx R) = {!!}
-- high-pc-≋ prot-err = {!!}
-- high-pc-≋ (β v) = {!!}
-- high-pc-≋ β-if-true = {!!}
-- high-pc-≋ β-if-false = {!!}
-- high-pc-≋ (β-let x) = {!!}
-- high-pc-≋ ref-static = {!!}
-- high-pc-≋ (ref?-ok x) = {!!}
-- high-pc-≋ (ref?-fail x) = {!!}
-- high-pc-≋ (ref x x₁) = {!!}
-- high-pc-≋ (deref x) = {!!}
-- high-pc-≋ assign-static = {!!}
-- high-pc-≋ (assign?-ok x x₁) = {!!}
-- high-pc-≋ (assign?-fail x x₁) = {!!}
-- high-pc-≋ (assign x x₁) = {!!}
-- high-pc-≋ (cast ⊢V v a) = {!!}
-- high-pc-≋ (if-cast-true x) = {!!}
-- high-pc-≋ (if-cast-false x) = {!!}
-- high-pc-≋ (fun-cast x x₁ i) = {!!}
-- high-pc-≋ (deref-cast x x₁) = {!!}
-- high-pc-≋ (assign?-cast x i) = {!!}
-- high-pc-≋ (assign-cast x x₁ i) = {!!}
-- high-pc-≋ (β-cast-pc x) = {!!}
-- high-pc-≋ (app-● x) = {!!}
-- high-pc-≋ if-● = {!!}
-- high-pc-≋ deref-● = {!!}
-- high-pc-≋ (assign-● x) = {!!}
