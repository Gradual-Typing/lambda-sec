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
open import Erasure
open import ErasedReduction

Reachable : Term → Set
Reachable M = Σ[ b ∈ 𝔹 ] ∃[ ℓ ] ∃[ μ ] ∃[ μ′ ] ∃[ pc ] (M ∣ μ ∣ pc —↠ₑ $ b of ℓ ∣ μ′)

error-unreachable : ∀ e → ¬ (Reachable (error e))
error-unreachable e ⟨ b , ℓ , μ , μ′ , pc , _ ∣ μ ∣ pc —→⟨ error→M ⟩ _ ⟩ = error⌿→ₑ refl error→M

●-unreachable : ¬ (Reachable ●)
●-unreachable ⟨ b , ℓ , μ , μ′ , pc , _ ∣ μ ∣ pc —→⟨ ●→M ⟩ _ ⟩ = ●⌿→ₑ refl ●→M

data Stub : Term → Set where
  stub-●       : Stub ●
  stub-error   : ∀ {e} → Stub (error e)
  stub-discard : ∀ {M} → Stub (discard M)

-- determinism-step : ∀ {M₁ M₂ N₁ N₂ μ μ₁ μ₂ pc}
--   → M₁ ∣ μ ∣ pc —→ₑ N₁ ∣ μ₁
--   → M₂ ∣ μ ∣ pc —→ₑ N₂ ∣ μ₂
--   → M₁ ≡ M₂
--   → Erased M₁
--   → Reachable N₁ → Reachable N₂
--   → N₁ ≡ N₂ × μ₁ ≡ μ₂

determinism : ∀ {M μ μ₁ μ₂ pc} {b₁ b₂ : 𝔹}
  → M ∣ μ ∣ pc —↠ₑ $ b₁ of low ∣ μ₁
  → M ∣ μ ∣ pc —↠ₑ $ b₂ of low ∣ μ₂
  → Erased M
  → b₁ ≡ b₂
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc ∎) e = refl
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc —→⟨ b₁→M ⟩ M↠b₂) e =
  contradiction b₁→M (const⌿→ₑ refl)
determinism ($ b₂ of ℓ ∣ μ ∣ pc —→⟨ b₂→M ⟩ M↠b₁) ($ b₂ of ℓ ∣ μ ∣ pc ∎) e =
  contradiction b₂→M (const⌿→ₑ refl)
determinism (M ∣ μ ∣ pc —→⟨ M→N₁ ⟩ N₁↠b₁) (M ∣ μ ∣ pc —→⟨ M→N₂ ⟩ N₂↠b₂) e =
  {!!}
