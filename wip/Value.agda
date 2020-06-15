module Value where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)


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

    V-ref : Location → Value

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

  ⊢ᵥtt :
      --------- Unit
    ⊢ᵥ V-tt ⦂ `⊤

  ⊢ᵥtrue :
      ------------ True
    ⊢ᵥ V-true ⦂ `𝔹

  ⊢ᵥfalse :
      ------------- False
    ⊢ᵥ V-false ⦂ `𝔹

  ⊢ᵥlabel : ∀ {𝓁}
      ------------------ Label
    → ⊢ᵥ V-label 𝓁 ⦂ `ℒ

  ⊢ᵥclos : ∀ {Δ : Context} {γ : Env} {T S M 𝓁̂₁ 𝓁̂₂}
    → γ ⊨ Δ
    → (⊢M : T ∷ Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ S)
      ---------------------------------------------- Closure
    → ⊢ᵥ V-clos < M , γ , ⊢M > ⦂ T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S

  ⊢ᵥproxy : ∀ {S T S′ T′ v 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′}
    → ⊢ᵥ v ⦂ S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T
      --------------------------------------------------------------------------------------- Proxy
    → ⊢ᵥ V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′ v ⦂ S′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T′

  ⊢ᵥref : ∀ {T n 𝓁₁ 𝓁₂}
      ----------------------------------- Ref
    → ⊢ᵥ V-ref ⟨ n , ⟨ 𝓁₁ , 𝓁₂ ⟩ ⟩ ⦂ Ref (l̂ 𝓁₂) T

  ⊢ᵥlab : ∀ {T v 𝓁}
    → ⊢ᵥ v ⦂ T
      --------------------------- Labeled
    → ⊢ᵥ V-lab 𝓁 v ⦂ Lab (l̂ 𝓁) T
