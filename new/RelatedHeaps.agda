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

-- TODO:
-- high-pc-≈ : ∀ {M₁ M₂ μ₁ μ₂ Σ}
--   → M₁ ∣ μ₁ ∣ Σ ∣ high —→ M₂ ∣ μ₂
--   → μ₁ ≈ μ₂
