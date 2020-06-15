module Memory where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import StaticsLIO
open import Value


data Cell (X : Set) : Set where
  _↦_ : Location → X → Cell X

Store = List (Cell (𝕋 × Value))
StoreTyping = List (Cell 𝕋)

lookup : (μ : Store) → Location → Maybe (𝕋 × Value)
lookup [] _ = nothing
lookup ( ⟨ n , ⟨ 𝓁₁ , 𝓁₂ ⟩ ⟩ ↦ ⟨ T , v ⟩ ∷ μ′ ) ⟨ n′ , ⟨ 𝓁₁′ , 𝓁₂′ ⟩ ⟩ with n ≟ₙ n′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
... | yes _ | yes _ | yes _ = just ⟨ T , v ⟩
... | _ | _ | _ = lookup μ′ ⟨ n′ , ⟨ 𝓁₁′ , 𝓁₂′ ⟩ ⟩

-- A few tests
private
  μ : Store
  μ = ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ↦ ⟨ `𝔹 , V-true ⟩ ∷
      ⟨ 0 , ⟨ l 0 , l 1 ⟩ ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷
      ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ↦ ⟨ `ℒ , V-label (l 0) ⟩ ∷ []

  _ : lookup μ ⟨ 0 , ⟨ l 1 , l 1 ⟩ ⟩ ≡ nothing
  _ = refl

  _ : lookup μ ⟨ 1 , ⟨ l 2 , l 2 ⟩ ⟩ ≡ just ⟨ `𝔹 , V-true ⟩
  _ = refl


-- StoreTyping
