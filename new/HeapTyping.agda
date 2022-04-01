{- Well-typedness of the heap -}

open import Data.Nat
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Types

module HeapTyping where

open import Utils
open import Heap
open import CC

infix 4 _⊢_

_⊢_ : HeapContext → Heap → Set
Σ ⊢ μ = ∀ {a A}
  → key _≟_ Σ a ≡ just A
  → ∃[ T ] ∃[ ℓ ] (A ≡ T of l ℓ) ×
                   (∃[ V ] (key _≟_ μ a ≡ just ⟨ V , ℓ ⟩) × ([] ; Σ ; l low ⊢ V ⦂ A))
