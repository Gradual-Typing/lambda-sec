module Value where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig renaming (ABT to Term)


mutual
  -- A closure is a term with an env
  data Clos : Set where
    <_,_,_> : ∀ {Δ T 𝓁̂₁ 𝓁̂₂} → (M : Term) → Env → Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → Clos

  data Value : Set where
    V-tt : Value

    V-true : Value
    V-false : Value

    V-label : ℒ → Value

    V-clos : Clos → Value

    {- V-proxy casts from (S ⇒ T) to (S′ ⇒ T′) , (𝓁̂₁ 𝓁̂₂) to (𝓁̂₁′ 𝓁̂₂′) -}
    V-proxy : (S T S′ T′  : 𝕋) → (𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ : ℒ̂)
            → S′ ≲ S → T ≲ T′
            → 𝓁̂₁′ ⊑̂ 𝓁̂₁ → 𝓁̂₂ ⊑̂ 𝓁̂₂′
            → Value
            → Value

    V-ref : ℕ → ℒ → ℒ → Value

    V-lab : ℒ → Value → Value

  Env : Set
  Env = List Value
