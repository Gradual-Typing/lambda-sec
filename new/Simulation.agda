module Simulation where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import Heap
open import CC
open import ErasedReduction
open import HeapTyping
open import WellTyped

open import Erasure
open import RelatedHeaps


sim : ∀ {Σ gc pc A M₁ M₂ μ₁ μ₁′ μ₂}
  → [] ; Σ ; gc ; pc ⊢ M₁ ⦂ A
  → Σ ⊢ μ₁
  → l pc ≾ gc
  → M₁ ∣ μ₁ ∣ Σ ∣ pc —→ M₂ ∣ μ₂
  → μ₁ ≈ μ₁′
    -----------------------------------------------------------------------
  → ∃[ μ₂′ ] (erase M₁ ∣ μ₁′ ∣ Σ ∣ pc —↠ₑ erase M₂ ∣ μ₂′) × (μ₂ ≈ μ₂′)
sim {M₁ = M₁} {M₂} {μ₁} {μ₁′} ⊢M₁ ⊢μ₁ pc≾gc (ξ {F = F} M₁→M₂) μ₁≈ =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , _ ⟩    = plug-inversion ⊢M₁ pc≾gc in
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈ ⟩ = sim ⊢M ⊢μ₁ pc≾gc′ M₁→M₂ μ₁≈ in
  ⟨ μ₂′ , erase-plug F eraseM₁↠eraseM₂ , μ₂≈ ⟩
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (ξ-err {F}) μ≈ = ⟨ μ₁′ , erase-plug-error F , μ≈ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (prot-val {V} {ℓ = ℓ} v) μ≈ with ℓ
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
sim {Σ} {M₁ = M₁} {M₂} {μ₁} {μ₁′} {μ₂} (⊢prot ⊢M) ⊢μ₁ pc≾gc (prot-ctx {ℓ = ℓ} M₁→M₂) μ₁≈ with ℓ
... | low  = {- This case is like ξ because pc ⋎ low = pc -}
  let ⟨ μ₂′ , eraseM₁↠eraseM₂ , μ₂≈ ⟩ = sim {μ₁ = μ₁} {μ₁′} ⊢M ⊢μ₁ (consis-join-≾ pc≾gc ≾-refl) M₁→M₂ μ₁≈ in
  ⟨ μ₂′ , prot-ctx-mult eraseM₁↠eraseM₂ , μ₂≈ ⟩
... | high = ⟨ erase-μ μ₂ , _ ∣ _ ∣ Σ ∣ _ —→⟨ ●-● ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , erase-≈ μ₂ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ prot-err μ≈ = {!!}
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (β {V} {N} {ℓ = ℓ} v) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β (erase-val-value v) ⟩ cong (prot low) eq ∣ _ ∣ Σ ∣ _ ≡∎ , μ≈ ⟩
  where
  eq : erase N [ erase V ] ≡ erase (N [ V ])
  eq = {!!}
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ app-● (erase-val-value v) ⟩ ● ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-if-true {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β-if-true ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ if-●     ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-if-false {ℓ = ℓ}) μ≈ with ℓ
... | low  = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ β-if-false ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ if-●      ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim _ ⊢μ₁ _ (β-let x) μ≈ = {!!}
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ ref-static μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ ref-static ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim _ ⊢μ₁ _ (ref?-ok x) _ = {!!}
sim _ ⊢μ₁ _ (ref?-fail x) _ = {!!}
sim _ ⊢μ₁ _ (ref x x₁) = {!!}
sim _ ⊢μ₁ _ (deref x) = {!!}
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ assign-static μ≈ =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign-static ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (assign?-ok {a = a} {ℓ} {ℓ₁} eq pc≼ℓ₁) μ₁≈ with ℓ
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-ok● ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
... | low with ℓ₁
...   | low =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-ok (μ₁≈ a eq) pc≼ℓ₁ ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
...   | high =
  let ⟨ V′ , eq′ ⟩ = μ₁≈ a eq in
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-ok eq′ pc≼ℓ₁ ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
sim {Σ} {μ₁′ = μ₁′} _ ⊢μ₁ _ (assign?-fail {a = a} {ℓ} {ℓ₁} eq pc⋠ℓ₁) μ₁≈ with ℓ
... | high = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-fail● ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
... | low with ℓ₁
... |   low = ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-fail (μ₁≈ a eq) pc⋠ℓ₁ ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
... |   high =
  let ⟨ V′ , eq′ ⟩ = μ₁≈ a eq in
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign?-fail eq′ pc⋠ℓ₁ ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ₁≈ ⟩
sim {Σ} {μ₁ = μ₁} {μ₁′} (⊢assign✓ {ℓ = ℓ′} ⊢a ⊢V pc≼ℓ′) ⊢μ₁ _ (assign {V} {a = a} {ℓ} {ℓ₁} v eq) μ₁≈
  with ℓ₁ | ℓ
... | low  | low  =
  ⟨ ⟨ a , erase V , low ⟩ ∷ μ₁′ ,
     _ ∣ _ ∣ Σ ∣ _ —→⟨ assign (erase-val-value v) (μ₁≈ a eq) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ , μ≈-low μ₁≈ ⟩
... | low  | high =  {- This case is impossible -}
 case canonical-ref ⊢a V-addr of λ where
 (Ref-addr eq₁ (<:-ty (<:-l ℓ≼ℓ′) (<:-ref A′<:A A<:A′))) →
   case <:-antisym A′<:A A<:A′ of λ where
   refl →
    let ⟨ _ , _ , eq′ , _ ⟩ = ⊢μ₁ _ eq₁ in
    case trans (sym eq) eq′ of λ where
    refl → contradiction ℓ≼ℓ′ λ ()  {- high ⋠ low -}
... | high | low  =
  let ⟨ V′ , eq′ ⟩ = μ₁≈ a eq in
  ⟨ ⟨ a , erase V , high ⟩ ∷ μ₁′  , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign (erase-val-value v) eq′ ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ ,
    μ≈-high μ₁≈ ⟩
... | high | high =
  ⟨ μ₁′ , _ ∣ _ ∣ Σ ∣ _ —→⟨ assign-● (erase-val-value v) ⟩ _ ∣ _ ∣ Σ ∣ _ ∎ ,
    μ≈-high-update μ₁≈ eq ⟩
sim _ ⊢μ₁ _ (cast ⊢V v a) = {!!}
sim _ ⊢μ₁ _ (if-cast-true x) = {!!}
sim _ ⊢μ₁ _ (if-cast-false x) = {!!}
sim _ ⊢μ₁ _ (fun-cast x x₁ i) = {!!}
sim _ ⊢μ₁ _ (deref-cast x x₁) = {!!}
sim _ ⊢μ₁ _ (assign?-cast x i) = {!!}
sim _ ⊢μ₁ _ (assign-cast x x₁ i) = {!!}
sim {μ₁′ = μ₁′} _ ⊢μ₁ _ (β-cast-pc v) μ≈ = ⟨ μ₁′ , _ ∣ _ ∣ _ ∣ _ ∎ , μ≈ ⟩
sim (⊢sub ⊢M A<:B)       ⊢μ₁ pc≾gc M₁→M₂     μ≈ = sim ⊢M ⊢μ₁ pc≾gc M₁→M₂ μ≈
sim (⊢sub-pc ⊢M gc<:gc′) ⊢μ₁ pc≾gc M₁→M₂     μ≈ = sim ⊢M ⊢μ₁ (≾-<: pc≾gc gc<:gc′) M₁→M₂ μ≈

