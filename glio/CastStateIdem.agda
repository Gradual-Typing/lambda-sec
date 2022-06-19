module CastStateIdem where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst; subst₂; trans)

open import Lemmas
open import StaticsGLIO
open import Store
open import Interp
open import WellTypedness


-- Matches program state ⟨ μ , pc ⟩ from a configuration.
infix 10 _▹_,_

data _▹_,_ : Result Conf → Store → ℒ → Set where

  ▹error : ∀ {μ pc err} → error err ▹ μ , pc

  ▹timeout : ∀ {μ pc} → timeout ▹ μ , pc

  ▹result : ∀ {μ μ′ v pc pc′}
    → μ′ ≡ μ
    → pc′ ≡ pc
    → result ⟨ μ , v , pc ⟩ ▹ μ′ , pc′

castT′-state-idem : ∀ {μ pc T₁ T₂ v}
  → (T₁≲T₂ : T₁ ≲ T₂)
  → μ ⊢ᵥ v ⦂ T₁
  → castT′ μ pc T₁ T₂ T₁≲T₂ v ▹ μ , pc
castT′-state-idem ≲-⊤ ⊢ᵥtt = ▹result refl refl
castT′-state-idem ≲-𝔹 ⊢ᵥtrue = ▹result refl refl
castT′-state-idem ≲-𝔹 ⊢ᵥfalse = ▹result refl refl
castT′-state-idem ≲-ℒ ⊢ᵥlabel = ▹result refl refl
castT′-state-idem (≲-⇒ _ _ _ _) (⊢ᵥclos ⊢γ ⊢M) = ▹result refl refl
castT′-state-idem (≲-⇒ _ _ _ _) (⊢ᵥproxy ⊢v) = ▹result refl refl
castT′-state-idem {v = V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩} (≲-Ref {ℓ̂₁} {ℓ̂₂} _ _ _ _) (⊢ᵥref eq)
  with ℓ̂₂
... | ¿ = ▹result refl refl
... | (l̂ ℓ₂′) with ℓ₂ ≟ ℓ₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {v = V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩} (≲-Ref {ℓ̂₁} {ℓ̂₂} _ _ _ _) (⊢ᵥref-dyn eq)
  with ℓ̂₂
... | ¿ = ▹result refl refl
... | (l̂ ℓ₂′) with ℓ₂ ≟ ℓ₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {μ} {pc} {v = V-lab ℓ v} (≲-Lab {ℓ̂₁} {ℓ̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab ℓ≼ℓ′ ⊢v)
  with (l̂ ℓ) ≾? ℓ̂₂
... | no  _ = ▹error
... | yes _ with castT′ μ pc T₁ T₂ T₁≲T₂ v | castT′-state-idem {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ▹result μ≡μ′ pc≡pc′ = ▹result μ≡μ′ pc≡pc′
...   | timeout | ▹timeout = ▹timeout
...   | error _ | ▹error = ▹error
castT′-state-idem {μ} {pc} {v = V-lab ℓ v} (≲-Lab {ℓ̂₁} {ℓ̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab-dyn ⊢v)
  with (l̂ ℓ) ≾? ℓ̂₂
... | no  _ = ▹error
... | yes _ with castT′ μ pc T₁ T₂ T₁≲T₂ v | castT′-state-idem {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ▹result μ≡μ′ pc≡pc′ = ▹result μ≡μ′ pc≡pc′
...   | timeout | ▹timeout = ▹timeout
...   | error _ | ▹error = ▹error


castT-state-idem : ∀ {μ pc T₁ T₂ v}
  → μ ⊢ᵥ v ⦂ T₁
  → castT μ pc T₁ T₂ v ▹ μ , pc
castT-state-idem {μ} {pc} {T₁} {T₂} {v} ⊢v with T₁ ≲? T₂
... | yes T₁≲T₂ = castT′-state-idem T₁≲T₂ ⊢v
... | no  _     = ▹error


castL-state-idem : ∀ {μ pc ℓ̂₁ ℓ̂₂}
  → (ℓ̂₁≾ℓ̂₂ : ℓ̂₁ ≾ ℓ̂₂)
  → castL μ pc ℓ̂₁ ℓ̂₂ ℓ̂₁≾ℓ̂₂ ▹ μ , pc
castL-state-idem {μ} {pc} {ℓ̂₁} {ℓ̂₂} ℓ̂₁≾ℓ̂₂ with (l̂ pc) ≾? ℓ̂₂
... | yes _ = ▹result refl refl
... | no  _ = ▹error
