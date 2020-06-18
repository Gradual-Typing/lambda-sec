module Store where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig renaming (ABT to Term)



-- Store (heap) location index
Location = ℕ × ℒ × ℒ

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


data Cell (X : Set) : Set where
  _↦_ : Location → X → Cell X

Store = List (Cell (𝕋 × Value))

lookup : ∀ {X} → (μ : List (Cell X)) → Location → Maybe X
lookup [] _ = nothing
lookup ( ⟨ n , ⟨ 𝓁₁ , 𝓁₂ ⟩ ⟩ ↦ x ∷ μ′ ) ⟨ n′ , ⟨ 𝓁₁′ , 𝓁₂′ ⟩ ⟩ with n ≟ₙ n′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
... | yes _ | yes _ | yes _ = just x
... | _ | _ | _ = lookup μ′ ⟨ n′ , ⟨ 𝓁₁′ , 𝓁₂′ ⟩ ⟩

-- Examples:
private
  μ : Store
  μ = ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ↦ ⟨ `𝔹 , V-true ⟩ ∷
      ⟨ 0 , ⟨ l 0 , l 1 ⟩ ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷
      ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ↦ ⟨ `ℒ , V-label (l 0) ⟩ ∷ []

  _ : lookup μ ⟨ 0 , ⟨ l 1 , l 1 ⟩ ⟩ ≡ nothing
  _ = refl

  _ : lookup μ ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ≡ just ⟨ `𝔹 , V-true ⟩
  _ = refl
