module HeapContext where

open import Data.List using (List; length)
open import Data.Maybe
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Types
open import Addr public

HalfHeapContext = List RawType
HeapContext     = HalfHeapContext × HalfHeapContext

lookup-Σ : HeapContext → Addr → Maybe RawType
lookup-Σ ⟨ Σᴸ , Σᴴ ⟩ (a[ low  ] n) = nth Σᴸ n
lookup-Σ ⟨ Σᴸ , Σᴴ ⟩ (a[ high ] n) = nth Σᴴ n

infix 10 _FreshIn_

_FreshIn_ : Addr → HeapContext → Set
(a[ low  ] n) FreshIn ⟨ Σᴸ , Σᴴ ⟩ = n ≡ length Σᴸ
(a[ high ] n) FreshIn ⟨ Σᴸ , Σᴴ ⟩ = n ≡ length Σᴴ
