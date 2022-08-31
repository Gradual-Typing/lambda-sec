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


module Reduction where

open import Frame public

infix 2 _∣_∣_∣_—→_∣_

data _∣_∣_∣_—→_∣_ : Term → Heap → HeapContext → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ Σ pc}
    → M        ∣ μ ∣ Σ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------------- ξ
    → plug M F ∣ μ ∣ Σ ∣ pc —→ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ Σ pc e}
      ---------------------------------------------- ξ-error
    → plug (error e) F ∣ μ ∣ Σ ∣ pc —→ error e ∣ μ

  prot-val : ∀ {V μ Σ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot ℓ V ∣ μ ∣ Σ ∣ pc —→ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ Σ pc ℓ}
    → M        ∣ μ ∣ Σ ∣ pc ⋎ ℓ —→ M′        ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot ℓ M ∣ μ ∣ Σ ∣ pc     —→ prot ℓ M′ ∣ μ′

  prot-err : ∀ {μ Σ pc ℓ e}
      --------------------------------------------------- ProtectContext
    → prot ℓ (error e) ∣ μ ∣ Σ ∣ pc —→ error e ∣ μ

  β : ∀ {V N μ Σ pc pc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ pc′ ] A ˙ N of ℓ) · V ∣ μ ∣ Σ ∣ pc —→ prot ℓ (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ Σ pc A ℓ}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of ℓ) A M N ∣ μ ∣ Σ ∣ pc —→ prot ℓ M ∣ μ

  β-if-false : ∀ {M N μ Σ pc A ℓ}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of ℓ) A M N ∣ μ ∣ Σ ∣ pc —→ prot ℓ N ∣ μ

  β-let : ∀ {V N μ Σ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ Σ ∣ pc —→ N [ V ] ∣ μ

  ref-static : ∀ {M μ Σ pc ℓ}
      ------------------------------------------------- RefStatic
    → ref[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ ref✓[ ℓ ] M ∣ μ

  ref?-ok : ∀ {M μ Σ pc ℓ}
    → pc ≼ ℓ
      ------------------------------------------------- RefNSUSuccess
    → ref?[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ ref✓[ ℓ ] M ∣ μ

  ref?-fail : ∀ {M μ Σ pc ℓ}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- RefNSUFail
    → ref?[ ℓ ] M ∣ μ ∣ Σ ∣ pc —→ error nsu-error ∣ μ

  ref : ∀ {V μ Σ pc n ℓ}
    → (v : Value V)
    → a[ ℓ ] n FreshIn Σ  {- address is fresh -}
      -------------------------------------------------------------------------------- Ref
    → ref✓[ ℓ ] V ∣ μ ∣ Σ ∣ pc —→ addr (a[ ℓ ] n) of low ∣ cons-μ (a[ ℓ ] n) V v μ

  deref : ∀ {V μ Σ pc v n ℓ ℓ₁}
    → lookup-μ μ (a[ ℓ₁ ] n) ≡ just ⟨ V , v ⟩
      --------------------------------------------------------------------- Deref
    → ! (addr (a[ ℓ₁ ] n) of ℓ) ∣ μ ∣ Σ ∣ pc —→ prot (ℓ₁ ⋎ ℓ) V ∣ μ

  assign-static : ∀ {L M μ Σ pc}
      ------------------------------------------------------- AssignStatic
    → L := M ∣ μ ∣ Σ ∣ pc —→ L :=✓ M ∣ μ

  assign?-ok : ∀ {M μ Σ pc n ℓ ℓ₁}
    → pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUSuccess
    → (addr (a[ ℓ₁ ] n) of ℓ) :=? M ∣ μ ∣ Σ ∣ pc —→ (addr (a[ ℓ₁ ] n) of ℓ) :=✓ M ∣ μ

  assign?-fail : ∀ {M μ Σ pc n ℓ ℓ₁}
    → ¬ pc ≼ ℓ₁
      ----------------------------------------------------------------------------- AssignNSUFail
    → (addr (a[ ℓ₁ ] n) of ℓ) :=? M ∣ μ ∣ Σ ∣ pc —→ error nsu-error ∣ μ

  assign : ∀ {V μ Σ pc n ℓ ℓ₁}
    → (v : Value V)
      ---------------------------------------------------------------------------------------------- Assign
    → (addr (a[ ℓ₁ ] n) of ℓ) :=✓ V ∣ μ ∣ Σ ∣ pc —→ $ tt of low ∣ cons-μ (a[ ℓ₁ ] n) V v μ

  {- Reduction rules about casts, active and inert: -}
  cast : ∀ {A B V M μ Σ pc} {c : Cast A ⇒ B}
    → (v : Value V)
    → (a : Active c)
    → ApplyCast V , c ↝ M
      -------------------------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ Σ ∣ pc —→ M ∣ μ

  if-cast-true : ∀ {M N μ Σ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastTrue
    → if ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ Σ ∣ pc —→ prot ℓ (cast-pc ⋆ M) ⟨ branch/c A ℓ c ⟩ ∣ μ

  if-cast-false : ∀ {M N μ Σ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      --------------------------------------------------------------------------------------------- IfCastFalse
    → if ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ Σ ∣ pc —→ prot ℓ (cast-pc ⋆ N) ⟨ branch/c A ℓ c ⟩ ∣ μ

  fun-cast : ∀ {V W μ Σ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ---------------------------------------------------------------- FunCast
    → (V ⟨ c ⟩) · W ∣ μ ∣ Σ ∣ pc —→ elim-fun-proxy V W i pc ∣ μ

  deref-cast : ∀ {V μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → Inert c
      ------------------------------------------------------ DerefCast
    → ! (V ⟨ c ⟩) ∣ μ ∣ Σ ∣ pc —→ ! V ⟨ out/c c ⟩ ∣ μ

  assign?-cast : ∀ {V M μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → (i : Inert c)
      ----------------------------------------------------------------------------- AssignNSUCast
    → (V ⟨ c ⟩) :=? M ∣ μ ∣ Σ ∣ pc —→ elim-ref-proxy V M i _:=?_ ∣ μ

  assign-cast : ∀ {V W μ Σ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Value W
    → (i : Inert c)
      --------------------------------------------------------------------------------------------- AssignCast
    → (V ⟨ c ⟩) :=✓ W ∣ μ ∣ Σ ∣ pc —→ elim-ref-proxy V W i _:=✓_ {- V := (W ⟨ in/c c ⟩) -} ∣ μ

  β-cast-pc : ∀ {V μ Σ pc g}
    → Value V
      ------------------------------------- CastPC
    → cast-pc g V ∣ μ ∣ Σ ∣ pc —→ V ∣ μ


{- Multi-step reduction -}
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
