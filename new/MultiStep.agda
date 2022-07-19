open import Types
open import Heap
open import CC
open import Frame


module MultiStep
  (_∣_∣_∣_—→_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set)
  (ξ : ∀ {M M′ F μ μ′ Σ pc} → M ∣ μ ∣ Σ ∣ pc —→ M′ ∣ μ′ → plug M F ∣ μ ∣ Σ ∣ pc —→ plug M′ F ∣ μ′)
  (ξ-prot : ∀ {M M′ μ μ′ Σ pc ℓ} → M ∣ μ ∣ Σ ∣ pc ⋎ ℓ —→ M′ ∣ μ′ → prot ℓ M ∣ μ ∣ Σ ∣ pc —→ prot ℓ M′ ∣ μ′)where

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

plug-mult : ∀ {M M′ μ μ′ Σ pc} (F : Frame)
  → M ∣ μ ∣ Σ ∣ pc —↠ M′ ∣ μ′
  → plug M F ∣ μ ∣ Σ ∣ pc —↠ plug M′ F ∣ μ′
plug-mult F (_ ∣ _ ∣ _ ∣ _ ∎) = _ ∣ _ ∣ _ ∣ _ ∎
plug-mult F (_ ∣ _ ∣ _ ∣ _ —→⟨ R ⟩ R*) = _ ∣ _ ∣ _ ∣ _ —→⟨ ξ {F = F} R ⟩ plug-mult F R*

prot-ctx-mult : ∀ {M M′ μ μ′ Σ pc ℓ}
  → M ∣ μ ∣ Σ ∣ pc ⋎ ℓ —↠ M′ ∣ μ′
  → prot ℓ M ∣ μ ∣ Σ ∣ pc —↠ prot ℓ M′ ∣ μ′
prot-ctx-mult (_ ∣ _ ∣ _ ∣ .(_ ⋎ _) ∎) = _ ∣ _ ∣ _ ∣ _ ∎
prot-ctx-mult (_ ∣ _ ∣ _ ∣ .(_ ⋎ _) —→⟨ R ⟩ R*) = _ ∣ _ ∣ _ ∣ _ —→⟨ ξ-prot R ⟩ prot-ctx-mult R*
