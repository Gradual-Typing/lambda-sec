open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC


module ErasedReduction where

open import Reduction public

infix 2 _∣_∣_∣_—→ₑ_∣_

data _∣_∣_∣_—→ₑ_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ Σ pc}
    → M        ∣ μ ∣ Σ ∣ pc —→ₑ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ Σ ∣ pc —→ₑ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ Σ pc e}
      ---------------------------------------------- ξ-error
    → plug (error e) F ∣ μ ∣ Σ ∣ pc —→ₑ error e ∣ μ

  prot-val : ∀ {V μ Σ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot ℓ V ∣ μ ∣ Σ ∣ pc —→ₑ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ Σ pc ℓ}
    → M        ∣ μ ∣ Σ ∣ pc ⋎ ℓ —→ₑ M′        ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot ℓ M ∣ μ ∣ Σ ∣ pc     —→ₑ prot ℓ M′ ∣ μ′

  prot-err : ∀ {μ Σ pc ℓ e}
      --------------------------------------------------- ProtectContext
    → prot ℓ (error e) ∣ μ ∣ Σ ∣ pc —→ₑ error e ∣ μ

  β : ∀ {V N μ Σ pc gc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ gc′ ] A ˙ N of ℓ) · V ∣ μ ∣ Σ ∣ pc —→ₑ prot ℓ (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ Σ pc A ℓ}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of ℓ) A M N ∣ μ ∣ Σ ∣ pc —→ₑ prot ℓ M ∣ μ

  β-if-false : ∀ {M N μ Σ pc A ℓ}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of ℓ) A M N ∣ μ ∣ Σ ∣ pc —→ₑ prot ℓ N ∣ μ

  β-let : ∀ {V N μ Σ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ Σ ∣ pc —→ₑ N [ V ] ∣ μ

  ref-static : ∀ {M μ Σ pc ℓ}
      ------------------------------------------------- RefStatic
    → ref[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ₑ ref✓[ ℓ ] M ∣ μ

  ref?-ok : ∀ {M μ Σ pc ℓ}
    → pc ≼ ℓ
      ------------------------------------------------- RefNSUSuccess
    → ref?[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ₑ ref✓[ ℓ ] M ∣ μ

  ref?-fail : ∀ {M μ Σ pc ℓ}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- RefNSUFail
    → ref?[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ₑ error nsu-error ∣ μ

  ref : ∀ {V μ Σ pc a ℓ}
    → Value V
    → a ≡ length Σ  {- address a is fresh -}
      ----------------------------------------------------------------- Ref
    → ref✓[ ℓ ] V ∣ μ ∣ Σ ∣ pc —→ₑ addr a of low ∣ ⟨ a , V , ℓ ⟩ ∷ μ

  deref : ∀ {V μ Σ pc a ℓ ℓ₁}
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
      ------------------------------------------------------- Deref
    → ! (addr a of ℓ) ∣ μ ∣ Σ ∣ pc —→ₑ prot (ℓ₁ ⋎ ℓ) V ∣ μ

  assign-static : ∀ {L M μ Σ pc}
      ----------------------------------------- AssignStatic
    → L := M ∣ μ ∣ Σ ∣ pc —→ₑ L :=✓ M ∣ μ

  assign?-ok : ∀ {V M μ Σ pc a ℓ ℓ₁}
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
    → pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUSuccess
    → (addr a of ℓ) :=? M ∣ μ ∣ Σ ∣ pc —→ₑ (addr a of ℓ) :=✓ M ∣ μ

  assign?-fail : ∀ {V M μ Σ pc a ℓ ℓ₁}
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
    → ¬ pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUFail
    → (addr a of ℓ) :=? M ∣ μ ∣ Σ ∣ pc —→ₑ error nsu-error ∣ μ

  assign : ∀ {V V₁ μ Σ pc a ℓ ℓ₁}
    → Value V
    → key _≟_ μ a ≡ just ⟨ V₁ , ℓ₁ ⟩
      --------------------------------------------------------------------- Assign
    → (addr a of ℓ) :=✓ V ∣ μ ∣ Σ ∣ pc —→ₑ $ tt of low ∣ ⟨ a , V , ℓ₁ ⟩ ∷ μ

  {- Reduction rules about casts, active and inert: -}
  cast : ∀ {A B V μ Σ pc} {c : Cast A ⇒ B}
    → (⊢V : [] ; Σ ; l low ; low ⊢ V ⦂ A)
    → (v : Value V)
    → (a : Active c)
      -------------------------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ Σ ∣ pc —→ₑ apply-cast V ⊢V v c a ∣ μ

  if-cast-true : ∀ {M N μ Σ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastTrue
    → if ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ Σ ∣ pc —→ₑ prot ℓ (cast-pc ⋆ M) ⟨ branch/c A ℓ c ⟩ ∣ μ

  if-cast-false : ∀ {M N μ Σ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastFalse
    → if ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ Σ ∣ pc —→ₑ prot ℓ (cast-pc ⋆ N) ⟨ branch/c A ℓ c ⟩ ∣ μ

  fun-cast : ∀ {V W μ Σ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ---------------------------------------------------------------- FunCast
    → (V ⟨ c ⟩) · W ∣ μ ∣ Σ ∣ pc —→ₑ elim-fun-proxy V W i pc ∣ μ

  deref-cast : ∀ {V μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → Inert c
      ------------------------------------------------------ DerefCast
    → ! (V ⟨ c ⟩) ∣ μ ∣ Σ ∣ pc —→ₑ ! V ⟨ out/c c ⟩ ∣ μ

  assign?-cast : ∀ {V M μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → (i : Inert c)
      ----------------------------------------------------------------------------- AssignNSUCast
    → (V ⟨ c ⟩) :=? M ∣ μ ∣ Σ ∣ pc —→ₑ elim-ref-proxy V M i _:=?_ ∣ μ

  assign-cast : ∀ {V W μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Value W
    → (i : Inert c)
      --------------------------------------------------------------------------------------------- AssignCast
    → (V ⟨ c ⟩) :=✓ W ∣ μ ∣ Σ ∣ pc —→ₑ elim-ref-proxy V W i _:=✓_ {- V := (W ⟨ in/c c ⟩) -} ∣ μ

  β-cast-pc : ∀ {V μ Σ pc g}
    → Value V
      ------------------------------------- CastPC
    → cast-pc g V ∣ μ ∣ Σ ∣ pc —→ₑ V ∣ μ

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


open import MultiStep _∣_∣_∣_—→ₑ_∣_ ξ prot-ctx public
  renaming (
    _∣_∣_∣_—↠_∣_ to _∣_∣_∣_—↠ₑ_∣_;
    _∣_∣_∣_∎ to _∣_∣_∣_∎ₑ;
    _∣_∣_∣_—→⟨_⟩_ to _∣_∣_∣_—→ₑ⟨_⟩_;
    _∣_∣_∣_≡∎ to _∣_∣_∣_≡∎ₑ)