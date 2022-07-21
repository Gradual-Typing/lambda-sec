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

{- Lemma: If discard M —↠ V then V ≡ ● -}
discard↠● : ∀ {M M₁ V μ μ′ Σ pc}
  → M ∣ μ ∣ Σ ∣ pc —↠ₑ V ∣ μ′ → M ≡ discard M₁ → Value V → V ≡ ●
discard↠● (M ∣ μ ∣ Σ ∣ pc ∎) refl ()
discard↠● (M ∣ μ ∣ Σ ∣ pc —→⟨ ξ {F = F} M→N ⟩ N↠V) eq v =
  contradiction eq (plug-not-discard _ F)
discard↠● (M ∣ μ ∣ Σ ∣ pc —→⟨ ξ-err {F} {e = e} ⟩ N↠V) eq v =
  contradiction eq (plug-not-discard (error e) F)
discard↠● (M ∣ μ ∣ Σ ∣ pc —→⟨ discard-ctx M→N ⟩ N↠V) refl v = discard↠● N↠V refl v
discard↠● (M ∣ μ ∣ Σ ∣ pc —→⟨ discard-err ⟩ err↠V) refl v with err↠V
... | error e ∣ _ ∣ _ ∣ _ ∎ = case v of λ ()
... | error e ∣ _ ∣ _ ∣ _ —→⟨ err→ ⟩ _ = contradiction err→ (error⌿→ refl)
discard↠● (M ∣ μ ∣ Σ ∣ pc —→⟨ β-discard x ⟩ ●↠V) refl v with ●↠V
... | ● ∣ _ ∣ _ ∣ _ ∎ = refl
... | ● ∣ _ ∣ _ ∣ _ —→⟨ ●→ ⟩ _ = contradiction ●→ (value⌿→ V-●)

deterministic : ∀ {M₁ M₂ N₁ N₂ μ μ₁ μ₂ Σ pc}
  → M₁ ∣ μ ∣ Σ ∣ pc —→ₑ N₁ ∣ μ₁
  → M₂ ∣ μ ∣ Σ ∣ pc —→ₑ N₂ ∣ μ₂
  → M₁ ≡ M₂
    -----------------------------------------------------------------------
  → (N₁ ≡ N₂) ⊎ (∃[ L₁ ] ∃[ L₂ ] (N₁ ≡ discard L₁) × (N₂ ≡ discard L₂))
deterministic (ξ r1) r2 eq = {!!}
deterministic ξ-err r2 eq = {!!}
deterministic (prot-val v) r2 eq = {!!}
deterministic (prot-ctx r1) r2 eq = {!!}
deterministic prot-err r2 eq = {!!}
deterministic (β v) (ξ {F = □· V} r) refl = contradiction r (value⌿→ V-ƛ)
deterministic (β v) (ξ {F = (V ·□) V-ƛ} r) refl = contradiction r (value⌿→ v)
deterministic (β v) (ξ-err {((ƛ[ pc ] A ˙ N of ℓ) ·□) V-ƛ}) refl = case v of λ ()
deterministic (β v) (β v†) refl = inj₁ refl
deterministic β-if-true (ξ {F = if□ A M N} r) refl = contradiction r (value⌿→ V-const)
deterministic β-if-true (ξ-err {if□ A M N}) ()
deterministic β-if-true β-if-true refl = inj₁ refl
deterministic β-if-false r2 eq = {!!}
deterministic (β-let x) r2 eq = {!!}
deterministic ref-static r2 eq = {!!}
deterministic (ref?-ok x) r2 eq = {!!}
deterministic (ref?-fail x) r2 eq = {!!}
deterministic (ref x x₁) r2 eq = {!!}
deterministic (deref x) r2 eq = {!!}
deterministic assign-static r2 eq = {!!}
deterministic (assign?-ok x x₁) r2 eq = {!!}
deterministic (assign?-fail x x₁) r2 eq = {!!}
deterministic (assign x x₁) r2 eq = {!!}
deterministic (cast ⊢V v a) r2 eq = {!!}
deterministic (if-cast-true x) r2 eq = {!!}
deterministic (if-cast-false x) r2 eq = {!!}
deterministic (fun-cast x x₁ i) r2 eq = {!!}
deterministic (deref-cast x x₁) r2 eq = {!!}
deterministic (assign?-cast x i) r2 eq = {!!}
deterministic (assign-cast x x₁ i) r2 eq = {!!}
deterministic (β-cast-pc x) r2 eq = {!!}
deterministic (app-● x) r2 eq = {!!}
deterministic if-● r2 eq = {!!}
deterministic deref-● r2 eq = {!!}
deterministic assign?-ok● r2 eq = {!!}
deterministic assign?-fail● r2 eq = {!!}
deterministic (assign-● x) r2 eq = {!!}
deterministic (discard-ctx r1) r2 eq = {!!}
deterministic discard-err r2 eq = {!!}
deterministic (β-discard x) r2 eq = {!!}

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
