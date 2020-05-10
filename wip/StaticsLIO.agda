module StaticsLIO where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-refl)
import Syntax

infixr 6 _[_]⇒[_]_

data ℒ : Set where
  l : ℕ → ℒ

data ℒ̂ : Set where
  ¿ : ℒ̂
  l̂ : ℒ → ℒ̂

-- Examples: low and high.
𝐿 : ℒ̂
𝐿 = l̂ (l 0)

𝐻 : ℒ̂
𝐻 = l̂ (l 1)

data 𝕋 : Set where
  `⊤ : 𝕋                    -- Unit
  `𝔹 : 𝕋                    -- Bool
  `ℒ : 𝕋                    -- IF Label
  Ref : ℒ̂ → 𝕋 → 𝕋           -- Ref 𝓁̂ T - reference
  Lab : ℒ̂ → 𝕋 → 𝕋           -- Lab 𝓁̂ T - labeled type
  _[_]⇒[_]_ : 𝕋 → ℒ̂ → ℒ̂ → 𝕋 -- T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂
