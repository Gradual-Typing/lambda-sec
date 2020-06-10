module Value where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig renaming (ABT to Term)


mutual
  -- A closure is a term with an env
  data Clos : Set where
    <_,_,_> : ∀ {Δ T S 𝓁̂₁ 𝓁̂₂} → (M : Term) → Env → T ∷ Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ S → Clos

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


infix 4 _⊨_
infix 4 ⊢ᵥ_⦂_

-- Well-typed environment γ under context Γ
data _⊨_ : Env → Context → Set
-- Well-typed values
data ⊢ᵥ_⦂_ : Value → 𝕋 → Set

data _⊨_ where

  ⊨-∅ : [] ⊨ []

  ⊨-∷ : ∀ {Γ γ v T}
    → ⊢ᵥ v ⦂ T
    → γ ⊨ Γ
      --------------
    → v ∷ γ ⊨ T ∷ Γ

data ⊢ᵥ_⦂_ where

  ⊢ᵥtt :    ⊢ᵥ V-tt ⦂ `⊤

  ⊢ᵥtrue :  ⊢ᵥ V-true ⦂ `𝔹

  ⊢ᵥfalse : ⊢ᵥ V-false ⦂ `𝔹

  ⊢ᵥlabel : ∀ {𝓁}
       ------------------
    → ⊢ᵥ V-label 𝓁 ⦂ `ℒ

  ⊢ᵥclos : ∀ {Δ : Context} {γ : Env} {T S M 𝓁̂₁ 𝓁̂₂}
    → γ ⊨ Δ
    → (⊢M : T ∷ Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ S)
      ----------------------------------------------
    → ⊢ᵥ V-clos < M , γ , ⊢M > ⦂ T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S
