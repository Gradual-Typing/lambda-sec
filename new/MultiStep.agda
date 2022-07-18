open import Types
open import Heap
open import CC


module MultiStep (_∣_∣_∣_—→_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set) where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)


infix  2 _∣_∣_∣_—↠_∣_
infixr 2 _∣_∣_∣_—→⟨_⟩_
infix  3 _∣_∣_∣_∎

data _∣_∣_∣_—↠_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set where

    _∣_∣_∣_∎ : ∀ M μ Σ pc
        -----------------------------------
      → M ∣ μ ∣ Σ ∣ pc —↠ M ∣ μ

    _∣_∣_∣_—→⟨_⟩_ : ∀ L μ Σ pc {M N μ′ μ″ Σ′}
      → L ∣ μ  ∣ Σ  ∣ pc —→ M ∣ μ′
      → M ∣ μ′ ∣ Σ′ ∣ pc —↠ N ∣ μ″
        -----------------------------------
      → L ∣ μ  ∣ Σ  ∣ pc —↠ N ∣ μ″

_∣_∣_∣_≡∎ : ∀ {M M′} → M ≡ M′ → ∀ μ Σ pc → M ∣ μ ∣ Σ ∣ pc —↠ M′ ∣ μ
M≡M′ ∣ μ ∣ Σ ∣ pc ≡∎ rewrite M≡M′ = _ ∣ _ ∣ _ ∣ _ ∎
