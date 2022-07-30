open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC


module ErasedReduction where

open import Reduction public

infix 2 _∣_∣_—→ₑ_∣_

data _∣_∣_—→ₑ_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ pc}
    → M        ∣ μ ∣ pc —→ₑ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ₑ plug M′ F ∣ μ′

  discard-ctx : ∀ {M M′ μ μ′ pc}
    → M         ∣ μ ∣ high —→ₑ M′         ∣ μ′
      --------------------------------------------------- DiscardContext
    → discard M ∣ μ ∣ pc   —→ₑ discard M′ ∣ μ′

  discard-val : ∀ {V μ pc}
    → Value V
      ------------------------------------ Discard
    → discard V ∣ μ ∣ pc —→ₑ ● ∣ μ

  β : ∀ {V N μ pc pc′ A}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ pc′ ] A ˙ N of low) · V ∣ μ ∣ pc —→ₑ N [ V ] ∣ μ

  β-if-true : ∀ {M N μ pc A}
      ----------------------------------------------------------- IfTrue
    → if ($ true of low) A M N ∣ μ ∣ pc —→ₑ M ∣ μ

  β-if-false : ∀ {M N μ pc A}
      ----------------------------------------------------------- IfFalse
    → if ($ false of low) A M N ∣ μ ∣ pc —→ₑ N ∣ μ

  β-let : ∀ {V N μ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ pc —→ₑ N [ V ] ∣ μ

  ref-static : ∀ {M μ pc ℓ}
      ------------------------------------------------- RefStatic
    → ref[ ℓ ] M ∣ μ ∣ pc —→ₑ ref✓[ ℓ ] M ∣ μ

  ref?-ok : ∀ {M μ pc ℓ}
      ------------------------------------------------- RefNSUSuccess
    → ref?[ ℓ ] M ∣ μ ∣ pc —→ₑ ref✓[ ℓ ] M ∣ μ

  ref : ∀ {V μ pc a ℓ}
    → Value V
      ----------------------------------------------------------------- Ref
    → ref✓[ ℓ ] V ∣ μ ∣ pc —→ₑ addr a of low ∣ ⟨ a , V , ℓ ⟩ ∷ μ

  deref-low : ∀ {V μ pc a}
    → key _≟_ μ a ≡ just ⟨ V , low ⟩
      ------------------------------------------------------- DerefLow
    → ! (addr a of low) ∣ μ ∣ pc —→ₑ V ∣ μ

  deref-high : ∀ {V μ pc a}
      ------------------------------------------------------- DerefHigh
    → ! (addr a of low) ∣ μ ∣ pc —→ₑ discard V ∣ μ

  assign-static : ∀ {L M μ pc}
      ----------------------------------------- AssignStatic
    → L := M ∣ μ ∣ pc —→ₑ L :=✓ M ∣ μ

  assign?-ok : ∀ {M μ pc a}
      -------------------------------------------------------------------- AssignNSUSuccess
    → (addr a of low) :=? M ∣ μ ∣ pc —→ₑ (addr a of low) :=✓ M ∣ μ

  assign : ∀ {V μ pc a ℓ}
    → Value V
      ------------------------------------------------------------------------ Assign
    → (addr a of low) :=✓ V ∣ μ ∣ pc —→ₑ $ tt of low ∣ ⟨ a , V , ℓ ⟩ ∷ μ

  {- Special rules that consume ● -}
  app-● : ∀ {V M μ pc}
    → Value V
      -------------------------------------- App●
    → ● · V ∣ μ ∣ pc —→ₑ discard M ∣ μ

  if-true-● : ∀ {M N μ pc A}
      -------------------------------------------- IfTrue●
    → if ● A M N ∣ μ ∣ pc —→ₑ discard M ∣ μ

  if-false-● : ∀ {M N μ pc A}
      -------------------------------------------- IfFalse●
    → if ● A M N ∣ μ ∣ pc —→ₑ discard N ∣ μ

  deref-● : ∀ {M μ pc}
      ----------------------------------- Deref●
    → ! ● ∣ μ ∣ pc —→ₑ discard M ∣ μ

  assign?-ok● : ∀ {M μ pc}
      ------------------------------------------ AssignNSUSuccess●
    → ● :=? M ∣ μ ∣ pc —→ₑ ● :=✓ M ∣ μ

  assign-● : ∀ {V μ pc}
    → Value V
      ------------------------------------------------------------------------ Assign●
    → ● :=✓ V ∣ μ ∣ pc —→ₑ $ tt of low ∣ μ {- skip the assignment -}

  {- Simulates rules that produce errors -}
  fail : ∀ {M μ pc e}
      ------------------------------------ Fail
    → M ∣ μ ∣ pc —→ₑ error e ∣ μ


infix  2 _∣_∣_—↠ₑ_∣_
infixr 2 _∣_∣_—→⟨_⟩_
infix  3 _∣_∣_∎

data _∣_∣_—↠ₑ_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

    _∣_∣_∎ : ∀ M μ pc
        -----------------------------------
      → M ∣ μ ∣ pc —↠ₑ M ∣ μ

    _∣_∣_—→⟨_⟩_ : ∀ L μ pc {M N μ′ μ″}
      → L ∣ μ  ∣ pc —→ₑ M ∣ μ′
      → M ∣ μ′ ∣ pc —↠ₑ N ∣ μ″
        -----------------------------------
      → L ∣ μ  ∣ pc —↠ₑ N ∣ μ″

_∣_∣_≡∎ : ∀ {M M′} → M ≡ M′ → ∀ μ pc → M ∣ μ ∣ pc —↠ₑ M′ ∣ μ
M≡M′ ∣ μ ∣ pc ≡∎ rewrite M≡M′ = _ ∣ _ ∣ _ ∎

plug-mult : ∀ {M M′ μ μ′ pc} (F : Frame)
  → M        ∣ μ ∣ pc —↠ₑ M′        ∣ μ′
  → plug M F ∣ μ ∣ pc —↠ₑ plug M′ F ∣ μ′
plug-mult F (_ ∣ _ ∣ _ ∎)            = _ ∣ _ ∣ _ ∎
plug-mult F (_ ∣ _ ∣ _ —→⟨ R ⟩ R*) = _ ∣ _ ∣ _ —→⟨ ξ {F = F} R ⟩ plug-mult F R*

discard-mult : ∀ {M M′ μ μ′ pc}
  → M         ∣ μ ∣ high —↠ₑ M′         ∣ μ′
  → discard M ∣ μ ∣ pc   —↠ₑ discard M′ ∣ μ′
discard-mult (_ ∣ _ ∣ _ ∎)            = _ ∣ _ ∣ _ ∎
discard-mult (_ ∣ _ ∣ _ —→⟨ R ⟩ R*) = _ ∣ _ ∣ _ —→⟨ discard-ctx R ⟩ discard-mult R*
