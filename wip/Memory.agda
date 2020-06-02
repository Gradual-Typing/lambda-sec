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
open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig renaming (ABT to Term)

mutual
  -- A closure is a term with an env
  data Clos : Set where
    <_,_> : Term → Env → Clos

  data Value : Set where
    V-tt : Value

    V-true : Value
    V-false : Value

    V-label : ℒ → Value

    V-clos : Clos → Value
    V-proxy : (T T′ S S′ : 𝕋) → (𝓁̂₁ 𝓁̂₁′ 𝓁̂₂ 𝓁̂₂′ : ℒ̂) → Clos → Value

    V-ref : ℕ → ℒ → ℒ → Value

    V-lab : ℒ → Value → Value

  Env : Set
  Env = List Value

-- A heap location maps address and labels to a value.
data Cell : Set where
  _,_,_↦_ : (loc : ℕ) → (𝓁₁ 𝓁₂ : ℒ) → 𝕋 × Value → Cell

Store : Set
Store = List Cell

-- Machine configuration after eval
Conf : Set
Conf = Store × Value × ℒ

data Error : Set where
  stuck : Error
  castError : Error
  NSUError : Error
  memAccError : Error

-- The evaluation either diverges, or runs into an error, or returns a value.
data Result (X : Set) : Set where
  diverge : Result X
  error : Error → Result X
  result : X → Result X


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
