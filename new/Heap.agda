module Heap where

open import Data.Nat using (_≟_)
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)

open import Utils
open import Types
open import HeapContext public
open import CC using (Term; Value)

{- n ↦ V -}
HalfHeap = List (RawAddr × (Σ[ V ∈ Term ] Value V))
Heap     = HalfHeap × HalfHeap

lookup-μ : Heap → Addr → Maybe (Σ[ V ∈ Term ] Value V)
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ low  ] n) = find _≟_ μᴸ n
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ high ] n) = find _≟_ μᴴ n

cons-μ : Addr → (V : Term) → Value V → Heap → Heap
cons-μ (a[ low  ] n) V v ⟨ μᴸ , μᴴ ⟩ = ⟨ ⟨ n , V , v ⟩ ∷ μᴸ , μᴴ ⟩
cons-μ (a[ high ] n) V v ⟨ μᴸ , μᴴ ⟩ = ⟨ μᴸ , ⟨ n , V , v ⟩ ∷ μᴴ ⟩
