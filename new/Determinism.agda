module Determinism where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; cong; sym)
open import Function using (case_of_)

open import Utils
open import Types
open import CC
open import TypeBasedCast
open import ErasedReduction

Reachable : Term → Set
Reachable M = Σ[ b ∈ 𝔹 ] ∃[ ℓ ] ∃[ μ ] ∃[ μ′ ] ∃[ pc ] (M ∣ μ ∣ pc —↠ₑ $ b of ℓ ∣ μ′)

error⌿↠const : ∀ {M μ μ′ pc ℓ ι} e (k : rep ι) → M ≡ error e → ¬ (M ∣ μ ∣ pc —↠ₑ $ k of ℓ ∣ μ′)
error⌿↠const e k eq (_ ∣ μ ∣ pc —→⟨ ξ {F = F} R ⟩ R*) = contradiction eq (plug-not-error _ F)
error⌿↠const e k eq (M ∣ μ ∣ pc —→⟨ fail ⟩ R*) = error⌿↠const _ k refl R*

error-not-reachable : ∀ e → ¬ (Reachable (error e))
error-not-reachable e ⟨ b , ℓ , μ , μ′ , pc , M↠b ⟩ = contradiction M↠b (error⌿↠const e b refl)

{- Constant does not step to reachable -}
const⌿→ : ∀ {M M′ μ μ′ pc ι ℓ} {k : rep ι} → M ≡ $ k of ℓ → Reachable M′ → ¬ (M ∣ μ ∣ pc —→ₑ M′ ∣ μ′)
const⌿→ eq r (ξ {F = F} R) = plug-not-const _ F eq
const⌿→ eq r fail = contradiction r (error-not-reachable _)

determinism : ∀ {M μ μ₁ μ₂ pc} {b₁ b₂ : 𝔹}
  → M ∣ μ ∣ pc —↠ₑ $ b₁ of low ∣ μ₁
  → M ∣ μ ∣ pc —↠ₑ $ b₂ of low ∣ μ₂
  → b₁ ≡ b₂
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc ∎) = refl
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc —→⟨ b₁→M ⟩ M↠b₂) =
  contradiction b₁→M (const⌿→ refl ⟨ _ , _ , _ , _ , _ , M↠b₂ ⟩)
determinism ($ b₂ of ℓ ∣ μ ∣ pc —→⟨ b₂→M ⟩ M↠b₁) ($ b₂ of ℓ ∣ μ ∣ pc ∎) =
  contradiction b₂→M (const⌿→ refl ⟨ _ , _ , _ , _ , _ , M↠b₁ ⟩)
determinism (M ∣ μ ∣ pc —→⟨ M→N₁ ⟩ N₁↠b₁) (M ∣ μ ∣ pc —→⟨ M→N₂ ⟩ N₂↠b₂) =
  {!!}
