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
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
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
castT′-state-idem {v = V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩} (≲-Ref {𝓁̂₁} {𝓁̂₂} _ _ _ _) (⊢ᵥref eq)
  with 𝓁̂₂
... | ¿ = ▹result refl refl
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {v = V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩} (≲-Ref {𝓁̂₁} {𝓁̂₂} _ _ _ _) (⊢ᵥref-dyn eq)
  with 𝓁̂₂
... | ¿ = ▹result refl refl
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | yes _ = ▹result refl refl
...   | no  _ = ▹error
castT′-state-idem {μ} {pc} {v = V-lab 𝓁 v} (≲-Lab {𝓁̂₁} {𝓁̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab 𝓁≼𝓁′ ⊢v)
  with (l̂ 𝓁) ≾? 𝓁̂₂
... | no  _ = ▹error
... | yes _ with castT′ μ pc T₁ T₂ T₁≲T₂ v | castT′-state-idem {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ▹result μ≡μ′ pc≡pc′ = ▹result μ≡μ′ pc≡pc′
...   | timeout | ▹timeout = ▹timeout
...   | error _ | ▹error = ▹error
castT′-state-idem {μ} {pc} {v = V-lab 𝓁 v} (≲-Lab {𝓁̂₁} {𝓁̂₂} {T₁} {T₂} _ T₁≲T₂) (⊢ᵥlab-dyn ⊢v)
  with (l̂ 𝓁) ≾? 𝓁̂₂
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


castL-state-idem : ∀ {μ pc 𝓁̂₁ 𝓁̂₂}
  → (𝓁̂₁≾𝓁̂₂ : 𝓁̂₁ ≾ 𝓁̂₂)
  → castL μ pc 𝓁̂₁ 𝓁̂₂ 𝓁̂₁≾𝓁̂₂ ▹ μ , pc
castL-state-idem {μ} {pc} {𝓁̂₁} {𝓁̂₂} 𝓁̂₁≾𝓁̂₂ with (l̂ pc) ≾? 𝓁̂₂
... | yes _ = ▹result refl refl
... | no  _ = ▹error
