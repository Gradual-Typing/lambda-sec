module Simulation where

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
open import Erasure
open import Utils


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
sim {μ₁′ = μ₁′} ξ-err μ≈ = ⟨ μ₁′ , {!!} , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ} (prot-val {V} {ℓ = ℓ} v) μ≈ with ℓ
... | high rewrite erase-stamp-high v = ⟨ μ₁′ , ● ∣ μ₁′ ∣ _ ∣ low ∎ , μ≈ ⟩
... | low  =
  ⟨ μ₁′ ,
    prot[ low ] erase V ∣ μ₁′ ∣ Σ ∣ low —→⟨ prot-val (erase-val-value v) ⟩ eq ∣ μ₁′ ∣ Σ ∣ low ≡∎ , μ≈ ⟩
  where
  eq =
    begin
     stamp-val (erase V) (erase-val-value v) low
     ≡⟨ stamp-val-low (erase-val-value v) ⟩
     erase V
     ≡⟨ cong erase (sym (stamp-val-low v)) ⟩
     erase (stamp-val V v low)
     ∎
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

