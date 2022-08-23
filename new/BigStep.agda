module BigStep where

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

infix 2 _∣_∣_∣_⇓_∣_∣_

{- only consider evaluation to values -}
data _∣_∣_∣_⇓_∣_∣_ : Term → Heap → HeapContext → StaticLabel → (V : Term) → Value V → Heap → Set where

  ⇓-val : ∀ {μ Σ pc V v}
      --------------------------- Value
    → V ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ

  ⇓-app : ∀ {μ μ₁ μ₂ μ₃ Σ Σ₁ Σ₂ pc pc′ L M N V W v w A ℓ}
    → L       ∣ μ  ∣ Σ  ∣ pc     ⇓ ƛ[ pc′ ] A ˙ N of ℓ ∣ V-ƛ ∣ μ₁
    → M       ∣ μ₁ ∣ Σ₁ ∣ pc     ⇓ V ∣ v ∣ μ₂
    → N [ V ] ∣ μ₂ ∣ Σ₂ ∣ pc ⋎ ℓ ⇓ W ∣ w ∣ μ₃
      ---------------------------------------------------------------------- Application
    → L · M ∣ μ ∣ Σ ∣ pc ⇓ stamp-val W w ℓ ∣ stamp-val-value w ∣ μ₃

  ⇓-if-true : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M N V v A ℓ}
    → L ∣ μ  ∣ Σ  ∣ pc     ⇓ $ true of ℓ ∣ V-const ∣ μ₁
    → M ∣ μ₁ ∣ Σ₁ ∣ pc ⋎ ℓ ⇓ V ∣ v ∣ μ₂
      ---------------------------------------------------------------------- IfTrue
    → if L A M N ∣ μ ∣ Σ ∣ pc ⇓ stamp-val V v ℓ ∣ stamp-val-value v ∣ μ₂

  ⇓-if-false : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M N V v A ℓ}
    → L ∣ μ  ∣ Σ  ∣ pc     ⇓ $ false of ℓ ∣ V-const ∣ μ₁
    → N ∣ μ₁ ∣ Σ₁ ∣ pc ⋎ ℓ ⇓ V ∣ v ∣ μ₂
      ---------------------------------------------------------------------- IfFalse
    → if L A M N ∣ μ ∣ Σ ∣ pc ⇓ stamp-val V v ℓ ∣ stamp-val-value v ∣ μ₂

  ⇓-let : ∀ {μ μ₁ μ₂ Σ Σ₁ pc M N V W v w}
    → M       ∣ μ  ∣ Σ  ∣ pc ⇓ V ∣ v ∣ μ₁
    → N [ V ] ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
      ----------------------------------------- Let
    → `let M N ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₂

  ⇓-ref? : ∀ {μ μ₁ Σ pc M V v ℓ}
    → ref[ ℓ ] M ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ₁
    → pc ≼ ℓ
      -------------------------------------- RefNSU
    → ref?[ ℓ ] M ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ₁

  ⇓-ref : ∀ {μ μ₁ Σ pc M V v n ℓ}
    → M ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ₁
    → a[ ℓ ] n FreshIn Σ
      ------------------------------------------------------------------------ Ref
    → ref[ ℓ ] M ∣ μ ∣ Σ ∣ pc ⇓ addr (a[ ℓ ] n) of low ∣ V-addr ∣ cons-μ (a[ ℓ ] n) V μ₁

  ⇓-deref : ∀ {μ μ₁ Σ pc M V n ℓ ℓ₁}
    → M ∣ μ ∣ Σ ∣ pc ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → lookup-μ μ (a[ ℓ₁ ] n) ≡ just V
      ---------------------------------------------------------------------------- Deref
    -- FIXME: our heap model probably need to store a proof of value
    → ! M ∣ μ ∣ Σ ∣ pc ⇓ stamp-val V {!!} (ℓ₁ ⋎ ℓ) ∣ stamp-val-value {!!} ∣ μ₁

  ⇓-assign? : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V v n ℓ ℓ₁}
    → L ∣ μ ∣ Σ ∣ pc ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → (addr (a[ ℓ₁ ] n) of ℓ) := M ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ V ∣ v ∣ μ₂
    → pc ≼ ℓ₁
      ------------------------------------------------- AssignNSU
    → L :=? M ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ₂

  ⇓-assign : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V v n ℓ ℓ₁}
    → L ∣ μ  ∣ Σ  ∣ pc ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → M ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ V ∣ v ∣ μ₂
      -------------------------------------------------------------------------- Assign
    → L := M ∣ μ ∣ Σ ∣ pc ⇓ $ tt of low ∣ V-const ∣ cons-μ (a[ ℓ₁ ] n) V μ₂

  ⇓-cast : ∀ {μ μ₁ μ₂ Σ Σ₁ pc M V W v w A B} {c : Cast A ⇒ B}
    → (a : Active c)
    → M ∣ μ ∣ Σ ∣ pc ⇓ V ∣ v ∣ μ₁
    → (⊢V : [] ; Σ ; l low ; low ⊢ V ⦂ A)
    → apply-cast V ⊢V v c a ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
      --------------------------------------------------------- Cast
    → M ⟨ c ⟩ ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₂

  ⇓-if-cast-true : ∀ {μ μ₁ μ₂ μ₃ Σ Σ₁ Σ₂ pc L M N V W v w A g ℓ}
                      {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → (i : Inert c)
    → L ∣ μ  ∣ Σ  ∣ pc     ⇓ $ true of ℓ ⟨ c ⟩ ∣ V-cast V-const i ∣ μ₁
    → M ∣ μ₁ ∣ Σ₁ ∣ pc ⋎ ℓ ⇓ V ∣ v ∣ μ₂    {- don't need casting PC to ⋆ in big step -}
    → V ⟨ branch/c A ℓ c ⟩ ∣ μ₂ ∣ Σ₂ ∣ pc ⇓ W ∣ w ∣ μ₃
      --------------------------------------------------------- IfCastTrue
    → if L A M N ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₃

  ⇓-if-cast-false : ∀ {μ μ₁ μ₂ μ₃ Σ Σ₁ Σ₂ pc L M N V W v w A g ℓ}
                       {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → (i : Inert c)
    → L ∣ μ  ∣ Σ  ∣ pc     ⇓ $ false of ℓ ⟨ c ⟩ ∣ V-cast V-const i ∣ μ₁
    → N ∣ μ₁ ∣ Σ₁ ∣ pc ⋎ ℓ ⇓ V ∣ v ∣ μ₂
    → V ⟨ branch/c A ℓ c ⟩ ∣ μ₂ ∣ Σ₂ ∣ pc ⇓ W ∣ w ∣ μ₃
      --------------------------------------------------------- IfCastFalse
    → if L A M N ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₃

  ⇓-fun-cast : ∀ {μ μ₁ μ₂ μ₃ Σ Σ₁ Σ₂ pc L M V V′ W v v′ w A B C D gc₁ gc₂ g₁ g₂}
                  {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → (i : Inert c)
    → L ∣ μ  ∣ Σ  ∣ pc ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → M ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
    → elim-fun-proxy V W i pc ∣ μ₂ ∣ Σ₂ ∣ pc ⇓ V′ ∣ v′ ∣ μ₃
      --------------------------------------------------------- FunCast
    → L · M ∣ μ ∣ Σ ∣ pc ⇓ V′ ∣ v′ ∣ μ₃

  ⇓-deref-cast : ∀ {μ μ₁ μ₂ Σ Σ₁ pc M V W v w A B g₁ g₂}
                    {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → M               ∣ μ  ∣ Σ  ∣ pc ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → ! V ⟨ out/c c ⟩ ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
      --------------------------------------------------------- DerefCast
    → ! M ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₂

  ⇓-assign?-cast : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V W v w A B g₁ g₂}
                      {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → L ∣ μ ∣ Σ ∣ pc ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → elim-ref-proxy V M i _:=?_ ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
      ----------------------------------------------------------- AssignNSUCast
    → L :=? M ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₂

  ⇓-assign-cast : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V W v w A B g₁ g₂}
                     {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → L ∣ μ ∣ Σ ∣ pc ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → elim-ref-proxy V M i _:=_ ∣ μ₁ ∣ Σ₁ ∣ pc ⇓ W ∣ w ∣ μ₂
      ----------------------------------------------------------- AssignCast
    → L := M ∣ μ ∣ Σ ∣ pc ⇓ W ∣ w ∣ μ₂
