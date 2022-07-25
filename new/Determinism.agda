module Determinism where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Utils
open import CC
open import TypeBasedCast
open import ErasedReduction

addr⌿→ : ∀ {M M′ μ μ′ Σ pc a ℓ} → M ≡ addr a of ℓ → ¬ (M ∣ μ ∣ Σ ∣ pc —→ₑ M′ ∣ μ′)
addr⌿→ eq (ξ {F = F} _) = plug-not-addr _ F eq
addr⌿→ eq (ξ-err {F} {e = e}) = plug-not-addr (error e) F eq

ƛ⌿→ : ∀ {M M′ μ μ′ Σ pc pc′ A N ℓ} → M ≡ ƛ[ pc′ ] A ˙ N of ℓ → ¬ (M ∣ μ ∣ Σ ∣ pc —→ₑ M′ ∣ μ′)
ƛ⌿→ eq (ξ {F = F} _) = plug-not-lam _ F eq
ƛ⌿→ eq (ξ-err {F} {e = e}) = plug-not-lam (error e) F eq

value⌿→ : ∀ {V M μ μ′ Σ pc} → Value V → ¬ (V ∣ μ ∣ Σ ∣ pc —→ₑ M ∣ μ′)
value⌿→ v (ξ R) = {!!}
value⌿→ v ξ-err = {!!}
value⌿→ (V-cast _ i) (cast _ _ a) = {!!}

error⌿→ : ∀ {M M′ μ μ′ Σ pc e} → M ≡ error e → ¬ (M ∣ μ ∣ Σ ∣ pc —→ₑ M′ ∣ μ′)
error⌿→ eq (ξ {F = F} R) = plug-not-error _ F eq
error⌿→ eq (ξ-err {F} {e = e}) = plug-not-error (error e) F eq

var⌿→ : ∀ {M M′ μ μ′ Σ pc x} → M ≡ ` x → ¬ (M ∣ μ ∣ Σ ∣ pc —→ₑ M′ ∣ μ′)
var⌿→ eq = {!!}

determinism : ∀ {M V₁ V₂ μ μ₁ μ₂ Σ pc}
  → M ∣ μ ∣ Σ ∣ pc —↠ₑ V₁ ∣ μ₁
  → M ∣ μ ∣ Σ ∣ pc —↠ₑ V₂ ∣ μ₂
  → Value V₁ → Value V₂
  → V₁ ≡ V₂
determinism (V₁ ∣ μ ∣ Σ ∣ pc ∎) (V₂ ∣ μ ∣ Σ ∣ pc ∎) v₁ v₂ = refl
determinism (V₁ ∣ μ ∣ Σ ∣ pc ∎) (V₁ ∣ μ ∣ Σ ∣ pc —→⟨ V₁→N ⟩ N↠V₂) v₁ v₂ =
  contradiction V₁→N (value⌿→ v₁)
determinism (V₂ ∣ μ ∣ Σ ∣ pc —→⟨ V₂→N ⟩ N↠V₁) (V₂ ∣ μ ∣ Σ ∣ pc ∎) v₁ v₂ =
  contradiction V₂→N (value⌿→ v₂)
determinism (M ∣ μ ∣ Σ ∣ pc —→⟨ M→N₁ ⟩ N₁↠V₁) (M ∣ μ ∣ Σ ∣ pc —→⟨ M→N₂ ⟩ N₂↠V₂) v1 v2 =
  {!!}
