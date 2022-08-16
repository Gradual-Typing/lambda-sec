module Heap where

open import Data.Nat using (_≟_)
open import Data.List
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)

open import Utils
open import Types
open import HeapContext public
open import CC using (Term)

{- n ↦ V -}
HalfHeap = List (RawAddr × Term)
Heap     = HalfHeap × HalfHeap

lookup-μ : Heap → Addr → Maybe Term
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ low  ] n) = find _≟_ μᴸ n
lookup-μ ⟨ μᴸ , μᴴ ⟩ (a[ high ] n) = find _≟_ μᴴ n

cons-μ : Addr → Term → Heap → Heap
cons-μ (a[ low  ] n) V ⟨ μᴸ , μᴴ ⟩ = ⟨ ⟨ n , V ⟩ ∷ μᴸ , μᴴ ⟩
cons-μ (a[ high ] n) V ⟨ μᴸ , μᴴ ⟩ = ⟨ μᴸ , ⟨ n , V ⟩ ∷ μᴴ ⟩
