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

infix 2 _∣_⊢_⇓_∣_∣_

{- only consider evaluation to values -}
data _∣_⊢_⇓_∣_∣_ : Heap → StaticLabel → Term → (V : Term) → Value V → Heap → Set where

  ⇓-val : ∀ {μ pc V v}
      --------------------------- Value
    → μ ∣ pc ⊢ V ⇓ V ∣ v ∣ μ

  ⇓-app : ∀ {μ μ₁ μ₂ μ₃ pc pc′ L M N V W v w A ℓ}
    → μ  ∣ pc     ⊢ L       ⇓ ƛ[ pc′ ] A ˙ N of ℓ ∣ V-ƛ ∣ μ₁
    → μ₁ ∣ pc     ⊢ M       ⇓ V ∣ v ∣ μ₂
    → μ₂ ∣ pc ⋎ ℓ ⊢ N [ V ] ⇓ W ∣ w ∣ μ₃
      ---------------------------------------------------------------------- Application
    → μ  ∣ pc     ⊢ L · M   ⇓ stamp-val W w ℓ ∣ stamp-val-value w ∣ μ₃

  ⇓-if-true : ∀ {μ μ₁ μ₂ pc L M N V v A ℓ}
    → μ  ∣ pc     ⊢ L ⇓ $ true of ℓ ∣ V-const ∣ μ₁
    → μ₁ ∣ pc ⋎ ℓ ⊢ M ⇓ V ∣ v ∣ μ₂
      ---------------------------------------------------------------------- IfTrue
    → μ  ∣ pc     ⊢ if L A M N ⇓ stamp-val V v ℓ ∣ stamp-val-value v ∣ μ₂

  ⇓-if-false : ∀ {μ μ₁ μ₂ pc L M N V v A ℓ}
    → μ  ∣ pc     ⊢ L ⇓ $ false of ℓ ∣ V-const ∣ μ₁
    → μ₁ ∣ pc ⋎ ℓ ⊢ N ⇓ V ∣ v ∣ μ₂
      ---------------------------------------------------------------------- IfFalse
    → μ  ∣ pc     ⊢ if L A M N ⇓ stamp-val V v ℓ ∣ stamp-val-value v ∣ μ₂

  ⇓-let : ∀ {μ μ₁ μ₂ pc M N V W v w}
    → μ  ∣ pc ⊢ M       ⇓ V ∣ v ∣ μ₁
    → μ₁ ∣ pc ⊢ N [ V ] ⇓ W ∣ w ∣ μ₂
      ----------------------------------------- Let
    → μ  ∣ pc ⊢ `let M N ⇓ W ∣ w ∣ μ₂

  ⇓-ref? : ∀ {μ μ₁ pc M V v n ℓ}
    → μ ∣ pc ⊢ M ⇓ V ∣ v ∣ μ₁
    → a[ ℓ ] n FreshIn μ
    → pc ≼ ℓ
      -------------------------------------------------------------------------------------- RefNSU
    → μ ∣ pc ⊢ ref?[ ℓ ] M ⇓ addr (a[ ℓ ] n) of low ∣ V-addr ∣ cons-μ (a[ ℓ ] n) V v μ₁

  ⇓-ref : ∀ {μ μ₁ pc M V v n ℓ}
    → μ ∣ pc ⊢ M ⇓ V ∣ v ∣ μ₁
    → a[ ℓ ] n FreshIn μ
      -------------------------------------------------------------------------------------- Ref
    → μ ∣ pc ⊢ ref[ ℓ ] M ⇓ addr (a[ ℓ ] n) of low ∣ V-addr ∣ cons-μ (a[ ℓ ] n) V v μ₁

  ⇓-deref : ∀ {μ μ₁ pc M V v n ℓ ℓ₁}
    → μ ∣ pc ⊢ M ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → lookup-μ μ (a[ ℓ₁ ] n) ≡ just ⟨ V , v ⟩
      ---------------------------------------------------------------------------- Deref
    → μ ∣ pc ⊢ ! M ⇓ stamp-val V v (ℓ₁ ⋎ ℓ) ∣ stamp-val-value v ∣ μ₁

  ⇓-assign? : ∀ {μ μ₁ μ₂ pc L M V v n ℓ ℓ₁}
    → μ  ∣ pc ⊢ L ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ V ∣ v ∣ μ₂
    → pc ≼ ℓ₁
      -------------------------------------------------------------------------- AssignNSU
    → μ ∣ pc ⊢ L :=? M ⇓ $ tt of low ∣ V-const ∣ cons-μ (a[ ℓ₁ ] n) V v μ₂

  ⇓-assign : ∀ {μ μ₁ μ₂ pc L M V v n ℓ ℓ₁}
    → μ  ∣ pc ⊢ L ⇓ addr (a[ ℓ₁ ] n) of ℓ ∣ V-addr ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ V ∣ v ∣ μ₂
      -------------------------------------------------------------------------- Assign
    → μ  ∣ pc ⊢ L := M ⇓ $ tt of low ∣ V-const ∣ cons-μ (a[ ℓ₁ ] n) V v μ₂

  ⇓-cast : ∀ {μ μ₁ μ₂ pc M N V W v w A B} {c : Cast A ⇒ B}
    → (a : Active c)
    → μ  ∣ pc ⊢ M ⇓ V ∣ v ∣ μ₁
    → ApplyCast V , c ↝ N
    → μ₁ ∣ pc ⊢ N ⇓ W ∣ w ∣ μ₂
      --------------------------------------------------------- Cast
    → μ  ∣ pc ⊢ M ⟨ c ⟩ ⇓ W ∣ w ∣ μ₂

  ⇓-if-cast-true : ∀ {μ μ₁ μ₂ μ₃ pc L M N V W v w A g ℓ}
                      {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → (i : Inert c)
    → μ  ∣ pc     ⊢ L ⇓ $ true of ℓ ⟨ c ⟩ ∣ V-cast V-const i ∣ μ₁
    → μ₁ ∣ pc ⋎ ℓ ⊢ M ⇓ V ∣ v ∣ μ₂    {- don't need casting PC to ⋆ in big step -}
    → μ₂ ∣ pc     ⊢ V ⟨ branch/c A ℓ c ⟩ ⇓ W ∣ w ∣ μ₃
      --------------------------------------------------------- IfCastTrue
    → μ  ∣ pc     ⊢ if L A M N ⇓ W ∣ w ∣ μ₃

  ⇓-if-cast-false : ∀ {μ μ₁ μ₂ μ₃ pc L M N V W v w A g ℓ}
                       {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → (i : Inert c)
    → μ  ∣ pc     ⊢ L ⇓ $ false of ℓ ⟨ c ⟩ ∣ V-cast V-const i ∣ μ₁
    → μ₁ ∣ pc ⋎ ℓ ⊢ N ⇓ V ∣ v ∣ μ₂
    → μ₂ ∣ pc     ⊢ V ⟨ branch/c A ℓ c ⟩ ⇓ W ∣ w ∣ μ₃
      --------------------------------------------------------- IfCastFalse
    → μ  ∣ pc     ⊢ if L A M N ⇓ W ∣ w ∣ μ₃

  ⇓-fun-cast : ∀ {μ μ₁ μ₂ μ₃ pc L M V V′ W v v′ w A B C D gc₁ gc₂ g₁ g₂}
                  {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → (i : Inert c)
    → μ  ∣ pc ⊢ L ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ W ∣ w ∣ μ₂
    → μ₂ ∣ pc ⊢ elim-fun-proxy V W i pc ⇓ V′ ∣ v′ ∣ μ₃
      --------------------------------------------------------- FunCast
    → μ  ∣ pc ⊢ L · M ⇓ V′ ∣ v′ ∣ μ₃

  ⇓-deref-cast : ∀ {μ μ₁ μ₂ pc M V W v w A B g₁ g₂}
                    {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → μ  ∣ pc ⊢ M ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → μ₁ ∣ pc ⊢ ! V ⟨ out/c c ⟩ ⇓ W ∣ w ∣ μ₂
      --------------------------------------------------------- DerefCast
    → μ  ∣ pc ⊢ ! M ⇓ W ∣ w ∣ μ₂

  ⇓-assign?-cast : ∀ {μ μ₁ μ₂ pc L M V W v w A B g₁ g₂}
                      {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → μ  ∣ pc ⊢ L ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → μ₁ ∣ pc ⊢ elim-ref-proxy V M i _:=?_ ⇓ W ∣ w ∣ μ₂
      ----------------------------------------------------------- AssignNSUCast
    → μ  ∣ pc ⊢ L :=? M ⇓ W ∣ w ∣ μ₂

  ⇓-assign-cast : ∀ {μ μ₁ μ₂ pc L M V W v w A B g₁ g₂}
                     {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → (i : Inert c)
    → μ  ∣ pc ⊢ L ⇓ V ⟨ c ⟩ ∣ V-cast v i ∣ μ₁
    → μ₁ ∣ pc ⊢ elim-ref-proxy V M i _:=_ ⇓ W ∣ w ∣ μ₂
      ----------------------------------------------------------- AssignCast
    → μ  ∣ pc ⊢ L := M ⇓ W ∣ w ∣ μ₂
