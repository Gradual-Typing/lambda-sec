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

error-unreachable : ∀ e → ¬ Reachable (error e)
error-unreachable e ⟨ b , ℓ , μ , μ′ , pc , _ ∣ μ ∣ pc —→⟨ error→M ⟩ _ ⟩ = error⌿→ₑ refl error→M

●-unreachable : ¬ Reachable ●
●-unreachable ⟨ b , ℓ , μ , μ′ , pc , _ ∣ μ ∣ pc —→⟨ ●→M ⟩ _ ⟩ = ●⌿→ₑ refl ●→M

discard-unreachable : ∀ M → ¬ Reachable (discard M)
discard-unreachable M ⟨ b , ℓ , μ , μ′ , pc , discard↠b ⟩ = contradiction discard↠b (discard⌿↠b _ refl)
  where
  discard⌿↠b : ∀ {M μ μ′ pc} N → N ≡ discard M → ¬ (N ∣ μ ∣ pc —↠ₑ $ b of ℓ ∣ μ′)
  discard⌿↠b N eq (_ ∣ _ ∣ _ —→⟨ ξ {F = F} R ⟩ _) = contradiction eq (plug-not-discard _ F)
  discard⌿↠b N eq (_ ∣ _ ∣ _ —→⟨ ξ-err {F} ⟩ _) = contradiction eq (plug-not-discard _ F)
  discard⌿↠b N eq (_ ∣ _ ∣ _ —→⟨ discard-ctx _ ⟩ discard↠b) = discard⌿↠b _ refl discard↠b
  discard⌿↠b N eq (_ ∣ _ ∣ _ —→⟨ discard-err ⟩ error↠b) = contradiction ⟨ _ , _ , _ , _ , _ , error↠b ⟩ (error-unreachable _)
  discard⌿↠b N eq (_ ∣ _ ∣ _ —→⟨ discard-val _ ⟩ ●↠b) = contradiction ⟨ _ , _ , _ , _ , _ , ●↠b ⟩ ●-unreachable

data Stub : Term → Set where
  stub-●       : Stub ●
  stub-error   : ∀ {e} → Stub (error e)
  stub-discard : ∀ {M} → Stub (discard M)

determinism-step : ∀ {M₁ M₂ N₁ N₂ μ μ₁ μ₂ pc}
  → M₁ ∣ μ ∣ pc —→ₑ N₁ ∣ μ₁
  → M₂ ∣ μ ∣ pc —→ₑ N₂ ∣ μ₂
  → M₁ ≡ M₂
  → Erased M₁
  → Reachable N₁ → Reachable N₂
    --------------------------------
  → N₁ ≡ N₂ × μ₁ ≡ μ₂
determinism-step (ξ R1) (ξ R2) eq _ r1 r2 = {!!}
determinism-step (ξ {F = □· _} ƛ→) (β v) refl = contradiction ƛ→ (ƛ⌿→ₑ refl)
determinism-step (ξ {F = (_ ·□) v} W→) (β w) refl (e-app _ erased-w) = contradiction W→ (V⌿→ₑ w erased-w)
determinism-step (ξ {F = if□ A M N} true→) β-if-true refl = contradiction true→ (const⌿→ₑ refl)
determinism-step (ξ {F = if□ A M N} false→) β-if-false refl = contradiction false→ (const⌿→ₑ refl)
determinism-step (ξ {F = let□ _} V→) (β-let v) refl (e-let erased-v _) = contradiction V→ (V⌿→ₑ v erased-v)
determinism-step (ξ {F = □· _} _) ref-static ()
determinism-step (ξ {F = □· _} _) ref?-ok ()
determinism-step (ξ {F = ref✓[ ℓ ]□} V→) (ref v) refl (e-ref✓ erased-v) = contradiction V→ (V⌿→ₑ v erased-v)
determinism-step (ξ {F = !□} addr→) (deref-low eq) refl e r1 r2 = contradiction addr→ (addr⌿→ₑ refl)
determinism-step (ξ R1) assign-static eq e r1 r2 = {!!}
determinism-step (ξ R1) assign?-ok eq e r1 r2 = {!!}
determinism-step (ξ R1) assign?-fail eq e r1 r2 = {!!}
determinism-step (ξ R1) (assign x) eq e r1 r2 = {!!}
determinism-step (ξ R1) (app-● x) eq e r1 r2 = {!!}
determinism-step (ξ R1) if-true-● eq e r1 r2 = {!!}
determinism-step (ξ R1) if-false-● eq e r1 r2 = {!!}
determinism-step (ξ R1) deref-● eq e r1 r2 = {!!}
determinism-step (ξ R1) assign?-ok● eq e r1 r2 = {!!}
determinism-step (ξ R1) assign?-fail● eq e r1 r2 = {!!}
determinism-step (ξ R1) (assign-● x) eq e r1 r2 = {!!}
determinism-step (β x) R2 eq e r1 r2 = {!!}
determinism-step β-if-true (ξ {F = if□ A M N} true→) refl = contradiction true→ (const⌿→ₑ refl)
determinism-step β-if-true β-if-true refl e r1 r2 = ⟨ refl , refl ⟩
determinism-step β-if-false R2 eq e r1 r2 = {!!}
determinism-step (β-let x) R2 eq e r1 r2 = {!!}
determinism-step ref-static R2 eq e r1 r2 = {!!}
determinism-step ref?-ok R2 eq e r1 r2 = {!!}
determinism-step (ref x) R2 eq e r1 r2 = {!!}
determinism-step (deref-low x) R2 eq e r1 r2 = {!!}
determinism-step assign-static R2 eq e r1 r2 = {!!}
determinism-step assign?-ok R2 eq e r1 r2 = {!!}
determinism-step assign?-fail R2 eq e r1 r2 = {!!}
determinism-step (assign x) R2 eq e r1 r2 = {!!}
determinism-step (app-● x) R2 eq e r1 r2 = {!!}
determinism-step if-true-● R2 eq e r1 r2 = {!!}
determinism-step if-false-● R2 eq e r1 r2 = {!!}
determinism-step deref-● R2 eq e r1 r2 = {!!}
determinism-step assign?-ok● R2 eq e r1 r2 = {!!}
determinism-step assign?-fail● R2 eq e r1 r2 = {!!}
determinism-step (assign-● x) R2 eq e r1 r2 = {!!}
determinism-step ξ-err _ eq _ r _           = contradiction r (error-unreachable _)
determinism-step _ ξ-err eq _ _ r           = contradiction r (error-unreachable _)
determinism-step _ (discard-ctx _) eq _ _ r = contradiction r (discard-unreachable _)
determinism-step (discard-ctx _) _ eq _ r _ = contradiction r (discard-unreachable _)
determinism-step _ discard-err eq _ _ r     = contradiction r (error-unreachable _)
determinism-step discard-err _ eq _ r _     = contradiction r (error-unreachable _)
determinism-step _ (discard-val v) eq _ _ r = contradiction r ●-unreachable
determinism-step (discard-val v) _ eq _ r _ = contradiction r ●-unreachable
determinism-step ref?-fail _ eq _ r _       = contradiction r (error-unreachable _)
determinism-step _ ref?-fail eq _ _ r       = contradiction r (error-unreachable _)
determinism-step deref-high _ eq _ r _      = contradiction r (discard-unreachable _)
determinism-step _ deref-high eq _ _ r      = contradiction r (discard-unreachable _)


determinism : ∀ {M μ μ₁ μ₂ pc} {b₁ b₂ : 𝔹}
  → M ∣ μ ∣ pc —↠ₑ $ b₁ of low ∣ μ₁
  → M ∣ μ ∣ pc —↠ₑ $ b₂ of low ∣ μ₂
  → Erased M
    -------------------------------------
  → b₁ ≡ b₂
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc ∎) e = refl
determinism ($ b₁ of ℓ ∣ μ ∣ pc ∎) ($ b₁ of ℓ ∣ μ ∣ pc —→⟨ b₁→M ⟩ M↠b₂) e =
  contradiction b₁→M (const⌿→ₑ refl)
determinism ($ b₂ of ℓ ∣ μ ∣ pc —→⟨ b₂→M ⟩ M↠b₁) ($ b₂ of ℓ ∣ μ ∣ pc ∎) e =
  contradiction b₂→M (const⌿→ₑ refl)
determinism (M ∣ μ ∣ pc —→⟨ M→N₁ ⟩ N₁↠b₁) (M ∣ μ ∣ pc —→⟨ M→N₂ ⟩ N₂↠b₂) e =
  {!!}
