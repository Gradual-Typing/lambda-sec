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

error⌿↠const : ∀ {M μ μ′ pc ℓ ι} e (k : rep ι) → M ≡ error e → ¬ (M ∣ μ ∣ pc —↠ₑ $ k of ℓ ∣ μ′)
error⌿↠const e k eq (_ ∣ μ ∣ pc —→⟨ ξ {F = F} R ⟩ R*) = contradiction eq (plug-not-error _ F)
error⌿↠const e k eq (M ∣ μ ∣ pc —→⟨ fail ⟩ R*) = error⌿↠const _ k refl R*

error-unreachable : ∀ e → ¬ (Reachable (error e))
error-unreachable e ⟨ b , ℓ , μ , μ′ , pc , M↠b ⟩ = contradiction M↠b (error⌿↠const e b refl)

●⌿↠const : ∀ {M μ μ′ pc ℓ ι} (k : rep ι) → M ≡ ● → ¬ (M ∣ μ ∣ pc —↠ₑ $ k of ℓ ∣ μ′)
●⌿↠const k eq (_ ∣ μ ∣ pc —→⟨ ξ {F = F} R ⟩ R*) = contradiction eq (plug-not-● _ F)
●⌿↠const k eq (M ∣ μ ∣ pc —→⟨ fail ⟩ R*) = error⌿↠const _ k refl R*
●⌿↠const k eq (M ∣ μ ∣ pc —→⟨ ●-● ⟩ R*) = ●⌿↠const k refl R*

●-unreachable : ¬ (Reachable ●)
●-unreachable ⟨ b , ℓ , μ , μ′ , pc , M↠b ⟩ = contradiction M↠b (●⌿↠const b refl)

{- Constant does not step to reachable -}
const⌿→reachable : ∀ {M M′ μ μ′ pc ι ℓ} {k : rep ι} → M ≡ $ k of ℓ → Reachable M′ → ¬ (M ∣ μ ∣ pc —→ₑ M′ ∣ μ′)
const⌿→reachable eq r (ξ {F = F} R) = plug-not-const _ F eq
const⌿→reachable eq r fail = contradiction r (error-unreachable _)

data Stub : Term → Set where
  stub-●    : Stub ●
  stub-error : ∀ {e} → Stub (error e)

value→stub : ∀ {V M μ μ′ pc}
  → V ∣ μ ∣ pc —→ₑ M ∣ μ′
  → Value V → Erased V
  → Stub M
value→stub (ξ {F = □⟨ c ⟩} R) (V-cast v i) ()
value→stub ●-● v _ = stub-●
value→stub fail v _ = stub-error

determinism-step : ∀ {M₁ M₂ N₁ N₂ μ μ₁ μ₂ pc}
  → M₁ ∣ μ ∣ pc —→ₑ N₁ ∣ μ₁
  → M₂ ∣ μ ∣ pc —→ₑ N₂ ∣ μ₂
  → M₁ ≡ M₂
  → Erased M₁
  → Reachable N₁ → Reachable N₂
  → N₁ ≡ N₂ × μ₁ ≡ μ₂
determinism-step (ξ R1) R2 eq r1 r2 = {!!}
determinism-step (prot-val v) R2 eq r1 r2 = {!!}
determinism-step (prot-ctx R1) R2 eq r1 r2 = {!!}
determinism-step (β x) (ξ R2) eq (e-app _ eV) r1 r2 = {!!}
determinism-step (β x) (β x₁) eq r1 r2 = {!!}
determinism-step (β x) fail eq r1 r2 = {!!}
determinism-step β-if-true R2 eq r1 r2 = {!!}
determinism-step β-if-false R2 eq r1 r2 = {!!}
determinism-step (β-let x) R2 eq r1 r2 = {!!}
determinism-step ref-static R2 eq r1 r2 = {!!}
determinism-step ref?-ok R2 eq r1 r2 = {!!}
determinism-step (ref x) R2 eq r1 r2 = {!!}
determinism-step deref-low R2 eq r1 r2 = {!!}
determinism-step deref-high R2 eq r1 r2 = {!!}
determinism-step assign-static R2 eq r1 r2 = {!!}
determinism-step assign?-ok R2 eq r1 r2 = {!!}
determinism-step (assign x) R2 eq r1 r2 = {!!}
determinism-step (app-● x) R2 eq r1 r2 = {!!}
determinism-step if-● R2 eq r1 r2 = {!!}
determinism-step deref-● R2 eq r1 r2 = {!!}
determinism-step assign?-ok● R2 eq r1 r2 = {!!}
determinism-step (assign-● x) R2 eq r1 r2 = {!!}
determinism-step ●-● R2 eq r1 r2 = {!!}
determinism-step fail R2 eq r1 r2 = {!!}

determinism : ∀ {M μ μ₁ μ₂ pc} {b₁ b₂ : 𝔹}
  → M ∣ μ ∣ pc —↠ₑ $ b₁ of low ∣ μ₁
  → M ∣ μ ∣ pc —↠ₑ $ b₂ of low ∣ μ₂
  → Erased M
  → b₁ ≡ b₂
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc ∎) e = refl
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc —→⟨ b₁→M ⟩ M↠b₂) e =
  contradiction b₁→M (const⌿→reachable refl ⟨ _ , _ , _ , _ , _ , M↠b₂ ⟩)
determinism ($ b₂ of ℓ ∣ μ ∣ pc —→⟨ b₂→M ⟩ M↠b₁) ($ b₂ of ℓ ∣ μ ∣ pc ∎) e =
  contradiction b₂→M (const⌿→reachable refl ⟨ _ , _ , _ , _ , _ , M↠b₁ ⟩)
determinism (M ∣ μ ∣ pc —→⟨ M→N₁ ⟩ N₁↠b₁) (M ∣ μ ∣ pc —→⟨ M→N₂ ⟩ N₂↠b₂) e =
  {!!}
