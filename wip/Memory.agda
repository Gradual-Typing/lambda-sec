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



-- A heap location maps address and labels to a value.
data Cell : Set where
  _,_,_↦_ : (loc : ℕ) → (𝓁₁ 𝓁₂ : ℒ) → 𝕋 × Value → Cell

Store : Set
Store = List Cell


lookup : (m : Store) → (loc : ℕ) → (𝓁₁ 𝓁₂ : ℒ) → Maybe (𝕋 × Value)
lookup [] _ _ _ = nothing
lookup ( loc , 𝓁₁ , 𝓁₂ ↦ ⟨ T , v ⟩ ∷ m′) loc′ 𝓁₁′ 𝓁₂′ with loc ≟ₙ loc′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
... | yes _ | yes _ | yes _ = just ⟨ T , v ⟩
... | _ | _ | _ = lookup m′ loc′ 𝓁₁′ 𝓁₂′

-- A few tests
private
  mem : Store
  mem = 1 , l 2 , l 2 ↦ ⟨ `𝔹 , V-true ⟩ ∷
        0 , l 0 , l 1 ↦ ⟨ `⊤ , V-tt ⟩ ∷
        1 , l 2 , l 2 ↦ ⟨ `ℒ , V-label (l 0) ⟩ ∷ []

  _ : lookup mem 0 (l 1) (l 1) ≡ nothing
  _ = refl

  _ : lookup mem 1 (l 2) (l 2) ≡ just ⟨ `𝔹 , V-true ⟩
  _ = refl
