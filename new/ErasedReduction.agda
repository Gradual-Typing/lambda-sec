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

  prot-val : ∀ {V μ pc}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot low V ∣ μ ∣ pc —→ₑ V ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ pc}
    → M          ∣ μ ∣ pc ⋎ low —→ₑ M′          ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot low M ∣ μ ∣ pc       —→ₑ prot low M′ ∣ μ′

  β : ∀ {V N μ pc pc′ A}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ pc′ ] A ˙ N of low) · V ∣ μ ∣ pc —→ₑ prot low (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ pc A}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of low) A M N ∣ μ ∣ pc —→ₑ prot low M ∣ μ

  β-if-false : ∀ {M N μ pc A}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of low) A M N ∣ μ ∣ pc —→ₑ prot low N ∣ μ

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
      ------------------------------------------------------- DerefLow
    → ! (addr a of low) ∣ μ ∣ pc —→ₑ prot low V ∣ μ

  deref-high : ∀ {μ pc a}
      ------------------------------------------------------- DerefHigh
    → ! (addr a of low) ∣ μ ∣ pc —→ₑ ● ∣ μ

  assign-static : ∀ {L M μ pc}
      ----------------------------------------- AssignStatic
    → L := M ∣ μ ∣ pc —→ₑ L :=✓ M ∣ μ

  assign?-ok : ∀ {M μ pc a}
      ----------------------------------------------------------------------------- AssignNSUSuccess
    → (addr a of low) :=? M ∣ μ ∣ pc —→ₑ (addr a of low) :=✓ M ∣ μ

  assign : ∀ {V μ pc a ℓ}
    → Value V
      --------------------------------------------------------------------- Assign
    → (addr a of low) :=✓ V ∣ μ ∣ pc —→ₑ $ tt of low ∣ ⟨ a , V , ℓ ⟩ ∷ μ

  {- Special rules that consume ● -}
  app-● : ∀ {V μ pc}
    → Value V
      ----------------------------------- App●
    → ● · V ∣ μ ∣ pc —→ₑ ● ∣ μ

  if-● : ∀ {M N μ pc A}
      ---------------------------------------- If●
    → if ● A M N ∣ μ ∣ pc —→ₑ ● ∣ μ

  deref-● : ∀ {μ pc}
      ----------------------------------- Deref●
    → ! ● ∣ μ ∣ pc —→ₑ ● ∣ μ

  assign?-ok● : ∀ {M μ pc}
      ------------------------------------------------------------------------ AssignNSUSuccess●
    → ● :=? M ∣ μ ∣ pc —→ₑ ● :=✓ M ∣ μ

  assign-● : ∀ {V μ pc}
    → Value V
      ------------------------------------------------------------------------ Assign●
    → ● :=✓ V ∣ μ ∣ pc —→ₑ $ tt of low ∣ μ {- skip the assignment -}

  ●-● : ∀ {μ μ′ pc}
      ------------------------------------ ●●
    → ● ∣ μ ∣ pc —→ₑ ● ∣ μ′

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

prot-ctx-mult : ∀ {M M′ μ μ′ pc}
  → M          ∣ μ ∣ pc ⋎ low —↠ₑ M′          ∣ μ′
  → prot low M ∣ μ ∣ pc       —↠ₑ prot low M′ ∣ μ′
prot-ctx-mult (_ ∣ _ ∣ _ ∎)            = _ ∣ _ ∣ _ ∎
prot-ctx-mult (_ ∣ _ ∣ _ —→⟨ R ⟩ R*) = _ ∣ _ ∣ _ —→⟨ prot-ctx R ⟩ prot-ctx-mult R*
