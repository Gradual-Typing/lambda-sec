module ErasedReduction where

open import Data.Unit using (⊤; tt)

open import Heap
open import Types
open import CC
open import Reduction


infix 2 _∣_∣_∣_—→ₑ_∣_

data _∣_∣_∣_—→ₑ_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set where

  r : ∀ {M M′ μ μ′ Σ pc}
    → M ∣ μ ∣ Σ ∣ pc —→  M′ ∣ μ′
      ------------------------------------- Reduction
    → M ∣ μ ∣ Σ ∣ pc —→ₑ M′ ∣ μ′

  {- Special rules that consume ● -}
  app-● : ∀ {V μ Σ pc}
    → Value V
      ----------------------------------- App●
    → ● · V ∣ μ ∣ Σ ∣ pc —→ₑ ● ∣ μ

  if-● : ∀ {M N μ Σ pc A}
      ---------------------------------------- If●
    → if ● A M N ∣ μ ∣ Σ ∣ pc —→ₑ ● ∣ μ

  deref-● : ∀ {μ Σ pc}
      ----------------------------------- Deref●
    → ! ● ∣ μ ∣ Σ ∣ pc —→ₑ ● ∣ μ

  assign?-ok● : ∀ {M μ Σ pc}
      ------------------------------------------------------------------------ AssignNSUSuccess●
    → ● :=? M ∣ μ ∣ Σ ∣ pc —→ₑ ● :=✓ M ∣ μ

  assign?-fail● : ∀ {M μ Σ pc}
      ------------------------------------------------------------------------ AssignNSUFail●
    → ● :=? M ∣ μ ∣ Σ ∣ pc —→ₑ error nsu-error ∣ μ

  assign-● : ∀ {V μ Σ pc}
    → Value V
      ------------------------------------------------------------------------ Assign●
    → ● :=✓ V ∣ μ ∣ Σ ∣ pc —→ₑ $ tt of low ∣ μ {- skip the assignment -}

  ●-● : ∀ {μ μ′ Σ pc}
      ------------------------------------ ●●
    → ● ∣ μ ∣ Σ ∣ pc —→ₑ ● ∣ μ′


open import MultiStep _∣_∣_∣_—→ₑ_∣_ public
  renaming (
    _∣_∣_∣_—↠_∣_ to _∣_∣_∣_—↠ₑ_∣_;
    _∣_∣_∣_∎ to _∣_∣_∣_∎ₑ;
    _∣_∣_∣_—→⟨_⟩_ to _∣_∣_∣_—→ₑ⟨_⟩_;
    _∣_∣_∣_≡∎ to _∣_∣_∣_≡∎ₑ)

r* : ∀ {Σ pc M M′ μ μ′} → M ∣ μ ∣ Σ ∣ pc —↠ M′ ∣ μ′ → M ∣ μ ∣ Σ ∣ pc —↠ₑ M′ ∣ μ′
r* (M ∣ μ ∣ Σ ∣ pc ∎) = M ∣ μ ∣ Σ ∣ pc ∎ₑ
r* (M ∣ μ ∣ Σ ∣ pc —→⟨ M→N ⟩ N↠M′) = M ∣ μ ∣ Σ ∣ pc —→ₑ⟨ r M→N ⟩ r* N↠M′
