module ErasedOK where

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

-- Does not contain error, opaque, or discard
data OK : Term → Set where

  ok-const : ∀ {ι} {k : rep ι} → OK ($ k of low)

  ok-addr : ∀ {a} → OK (addr a of low)

  ok-var : ∀ {x} → OK (` x)

  ok-ƛ : ∀ {pc A N} → OK (ƛ[ pc ] A ˙ N of low)

  ok-app : ∀ {L M} → OK L → OK M → OK (L · M)

  ok-if : ∀ {A L M N} → OK L → OK M → OK N → OK (if L A M N)

  ok-let : ∀ {M N} → OK M → OK N → OK (`let M N)

  ok-ref : ∀ {M ℓ} → OK M → OK (ref[ ℓ ] M)

  ok-ref? : ∀ {M ℓ} → OK M → OK (ref?[ ℓ ] M)

  ok-ref✓ : ∀ {M ℓ} → OK M → OK (ref✓[ ℓ ] M)

  ok-deref : ∀ {M} → OK M → OK (! M)

  ok-assign : ∀ {L M} → OK L → OK M → OK (L := M)

  ok-assign? : ∀ {L M} → OK L → OK M → OK (L :=? M)

  ok-assign✓ : ∀ {L M} → OK L → OK M → OK (L :=✓ M)


reachable-is-ok : ∀ {M μ μ′ pc} {b : 𝔹} → M ∣ μ ∣ pc —↠ₑ $ b of low ∣ μ′ → OK M
reachable-is-ok ($ b of low ∣ _ ∣ _ ∎) = ok-const
reachable-is-ok (M ∣ μ ∣ pc —→⟨ R ⟩ R*) = {!!}
