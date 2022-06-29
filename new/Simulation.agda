module Simulation where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Reduction
open import Erasure
open import Utils

erase-stamp-high : ∀ {V} (v : Value V) → erase (stamp-val V v high) ≡ ●
erase-stamp-high (V-addr {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-ƛ {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-const {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-cast v i) = {!!}
erase-stamp-high V-● = refl


{- Related heaps -}
_≈_ : ∀ (μ μ′ : Heap) → Set
μ ≈ μ′ = ∀ a {V}
  → key _≟_ μ a ≡ just ⟨ V , low ⟩
  → ∃[ V′ ] (key _≟_ μ′ a ≡ just ⟨ V′ , low ⟩) × (V′ ≡ erase V)

sim : ∀ {M₁ M₂ μ₁ μ₂ μ₁′ Σ}
  → M₁ ∣ μ₁ ∣ Σ ∣ low —→ M₂ ∣ μ₂
  → μ₁ ≈ μ₁′
    -----------------------------------------------------------------------
  → ∃[ μ₂′ ] (erase M₁ ∣ μ₁′ ∣ Σ ∣ low —↠ erase M₂ ∣ μ₂′) × (μ₂ ≈ μ₂′)
sim (ξ R) μ≈ = {!!}
sim ξ-err μ≈ = {!!}
sim {μ₁′ = μ₁′} (prot-val {ℓ = ℓ} v) μ≈ with ℓ
... | high = ⟨ μ₁′ , {!!} , μ≈ ⟩
... | low  = {!!}
sim (prot-ctx R) μ≈ = {!!}
sim prot-err μ≈ = {!!}
sim (β x) μ≈ = {!!}
sim β-if-true μ≈ = {!!}
sim β-if-false μ≈ = {!!}
sim (β-let x) μ≈ = {!!}
sim ref-static μ≈ = {!!}
sim (ref?-ok x) _ = {!!}
sim (ref?-fail x) _ = {!!}
sim (ref x x₁) = {!!}
sim (deref x) = {!!}
sim assign-static = {!!}
sim (assign?-ok x x₁) = {!!}
sim (assign?-fail x x₁) = {!!}
sim (assign x x₁) = {!!}
sim (cast ⊢V v a) = {!!}
sim (if-cast-true x) = {!!}
sim (if-cast-false x) = {!!}
sim (fun-cast x x₁ i) = {!!}
sim (deref-cast x x₁) = {!!}
sim (assign?-cast x i) = {!!}
sim (assign-cast x x₁ i) = {!!}
sim (β-cast-pc x) _ = {!!}
sim (app-● x) _ = {!!}
sim if-● _ = {!!}
sim deref-● _ = {!!}
sim (assign-● x) _ = {!!}

