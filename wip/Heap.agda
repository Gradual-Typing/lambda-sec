module Heap where

open import Data.Nat using (zero; suc)
open import Data.Bool using (true; false)

open import TargetLang public


data WTStore : ∀ (Γ Σ Σ′ : Context) → Set where
  ε : ∀ {Γ Σ} →
      -----------
    WTStore Γ Σ ∅

  _,_ : ∀ {Γ Σ Σ′ A} {V : Γ ; Σ ; ᴸ ⊢ A}
    → WTStore Γ Σ Σ′
    → Value V
      ---------------------
    → WTStore Γ Σ (Σ′ , A)

Store : ∀ (Γ Σ : Context) → Set
Store Γ Σ = WTStore Γ Σ Σ

-- Examples:
Σ : Context
Σ = ∅ , ` `ℕ ^ ᴴ , ` `𝔹 ^ ᴸ , (` `ℕ ^ ᴴ) ⟦ ᴸ ⟧⇒ (` `ℕ ^ ᴴ) ^ ᴸ

σ : Store ∅ Σ
σ = ε , V-const {k = 0} {s = ᴴ} , V-const {k = false} {s = ᴸ} , V-ƛ {N = ` Z} {s = ᴸ}
