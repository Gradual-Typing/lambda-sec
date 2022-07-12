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
open import Utils

open import Erasure
open import RelatedHeaps


sim : ∀ {M₁ M₂ μ₁ μ₁′ μ₂ Σ pc}
  → M₁ ∣ μ₁ ∣ Σ ∣ pc —→ M₂ ∣ μ₂
  → μ₁ ≈ μ₁′
    -----------------------------------------------------------------------
  → ∃[ μ₂′ ] (erase M₁ ∣ μ₁′ ∣ Σ ∣ pc —↠ erase M₂ ∣ μ₂′) × (μ₂ ≈ μ₂′)
sim {M₁} {M₂} {μ₁} {μ₁′} (ξ {F = F} M₁→M₂) μ₁≈ =
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈ ⟩ = sim {μ₁ = μ₁} {μ₁′} M₁→M₂ μ₁≈ in
    ⟨ μ₂′ , erase-plug F eraseM₁↠eraseM₂ , μ₂≈ ⟩
sim {μ₁′ = μ₁′} (ξ-err {F}) μ≈ = ⟨ μ₁′ , erase-plug-error F , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} (prot-val {V} {ℓ = ℓ} v) μ≈ with ℓ
... | high rewrite erase-stamp-high v = ⟨ μ₁′ , ● ∣ μ₁′ ∣ _ ∣ _ ∎ , μ≈ ⟩
... | low  =
  ⟨ μ₁′ , prot low (erase V) ∣ μ₁′ ∣ Σ ∣ _ —→⟨ prot-val (erase-val-value v) ⟩ eq ∣ μ₁′ ∣ Σ ∣ _ ≡∎ , μ≈ ⟩
  where
  eq =
    begin
     stamp-val (erase V) (erase-val-value v) low
     ≡⟨ stamp-val-low (erase-val-value v) ⟩
     erase V
     ≡⟨ cong erase (sym (stamp-val-low v)) ⟩
     erase (stamp-val V v low)
     ∎
sim {M₁} {M₂} {μ₁} {μ₁′} {μ₂} {Σ = Σ} (prot-ctx {ℓ = ℓ} M₁→M₂) μ₁≈ with ℓ
... | low  = {- This case is like ξ because pc ⋎ low = pc -}
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈ ⟩ = sim {μ₁ = μ₁} {μ₁′} M₁→M₂ μ₁≈ in
  ⟨ μ₂′ , prot-ctx-mult eraseM₁↠eraseM₂ , μ₂≈ ⟩
... | high = {!!}
sim prot-err μ≈ = {!!}
sim {μ₁′ = μ₁′} {Σ = Σ} (β {V} {N} {ℓ = ℓ} v) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β (erase-val-value v) ⟩ cong (prot low) eq ∣ _ ∣ Σ ∣ _ ≡∎ , μ≈ ⟩
  where
  eq : erase N [ erase V ] ≡ erase (N [ V ])
  eq = {!!}
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ app-● (erase-val-value v) ⟩ ● ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} (β-if-true {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β-if-true ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ if-●     ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} (β-if-false {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β-if-false ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ if-●      ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim (β-let x) μ≈ = {!!}
sim {μ₁′ = μ₁′} {Σ = Σ} ref-static μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ ref-static ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim (ref?-ok x) _ = {!!}
sim (ref?-fail x) _ = {!!}
sim (ref x x₁) = {!!}
sim (deref x) = {!!}
sim assign-static = {!!}
sim (assign?-ok x x₁) = {!!}
sim (assign?-fail x x₁) = {!!}
sim {μ₁ = μ₁} {μ₁′} {Σ = Σ} (assign {V} {a = a} {ℓ} {ℓ₁} v eq) μ₁≈
  with ℓ₁ | ℓ
... | low  | low  =
  ⟨ ⟨ a , erase V , low ⟩ ∷ μ₁′ ,
     _ ∣ _ ∣ Σ ∣ _ —→⟨ assign (erase-val-value v) (μ₁≈ a eq) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈-low μ₁≈ ⟩
... | low  | high = {!!} {- Need to discriminate this case -}
... | high | low  =
  ⟨ {!!} , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign (erase-val-value v) {!!} ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , {!!} ⟩
... | high | high =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign-● (erase-val-value v) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ ,
    μ≈-high-update μ₁≈ eq ⟩
sim (cast ⊢V v a) = {!!}
sim (if-cast-true x) = {!!}
sim (if-cast-false x) = {!!}
sim (fun-cast x x₁ i) = {!!}
sim (deref-cast x x₁) = {!!}
sim (assign?-cast x i) = {!!}
sim (assign-cast x x₁ i) = {!!}
sim {μ₁′ = μ₁′} (β-cast-pc v) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} (app-● v) μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ app-● (erase-val-value v) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} if-● μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ if-● ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} deref-● μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ deref-● ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {μ₁′ = μ₁′} {Σ = Σ} (assign-● v) μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign-● (erase-val-value v) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩

