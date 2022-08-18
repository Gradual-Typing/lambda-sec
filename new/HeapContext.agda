module HeapContext where

open import Data.Nat
open import Data.List
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

infix 4 _⊇_

_⊇_ : ∀ (Σ′ Σ : HeapContext) → Set
Σ′ ⊇ Σ = ∀ a {T} → lookup-Σ Σ a ≡ just T → lookup-Σ Σ′ a ≡ just T

⊇-refl : ∀ Σ → Σ ⊇ Σ
⊇-refl Σ a eq = eq

{- extending the heap context -}
ext-Σ : StaticLabel → RawType → HeapContext → HeapContext
ext-Σ low  T ⟨ Σᴸ , Σᴴ ⟩ = ⟨ Σᴸ ∷ʳ T , Σᴴ ⟩
ext-Σ high T ⟨ Σᴸ , Σᴴ ⟩ = ⟨ Σᴸ , Σᴴ ∷ʳ T ⟩

⊇-ext : ∀ ℓ T Σ → ext-Σ ℓ T Σ ⊇ Σ
⊇-ext low  T ⟨ _ ∷ Σᴸ , Σᴴ ⟩ (a[ low ] 0) eq = eq
⊇-ext low  T ⟨ _ ∷ Σᴸ , Σᴴ ⟩ (a[ low ] (suc n)) eq = ⊇-ext low T ⟨ Σᴸ , Σᴴ ⟩ (a[ low ] n) eq
⊇-ext high T ⟨ _ ∷ Σᴸ , Σᴴ ⟩ (a[ low ] _) eq = eq
⊇-ext high T ⟨ Σᴸ , _ ∷ Σᴴ ⟩ (a[ high ] 0) eq = eq
⊇-ext high T ⟨ Σᴸ , _ ∷ Σᴴ ⟩ (a[ high ] (suc n)) eq = ⊇-ext high T ⟨ Σᴸ , Σᴴ ⟩ (a[ high ] n) eq
⊇-ext low  T ⟨ Σᴸ , _ ∷ Σᴴ ⟩ (a[ high ] _) eq = eq
