module BigStepErased where

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

infix 2 _∣_⊢_⇓ₑ_∣_∣_

{- runs on erased terms -}
data _∣_⊢_⇓ₑ_∣_∣_ : HalfHeap → StaticLabel → Term → (V : Term) → Value V → HalfHeap → Set where

  ⇓ₑ-val : ∀ {μ pc V v}
      --------------------------- Value
    → μ ∣ pc ⊢ V ⇓ₑ V ∣ v ∣ μ

  ⇓ₑ-app : ∀ {μ μ₁ μ₂ μ₃ pc pc′ L M N V W v w A}
    → μ  ∣ pc ⊢ L       ⇓ₑ ƛ[ pc′ ] A ˙ N of low ∣ V-ƛ ∣ μ₁
    → μ₁ ∣ pc ⊢ M       ⇓ₑ V ∣ v ∣ μ₂
    → μ₂ ∣ pc ⊢ N [ V ] ⇓ₑ W ∣ w ∣ μ₃
      ---------------------------------------- Application
    → μ  ∣ pc ⊢ L · M   ⇓ₑ W ∣ w ∣ μ₃

  ⇓ₑ-app-● : ∀ {μ μ₁ μ₂ pc L M V v}
    → μ  ∣ pc ⊢ L       ⇓ₑ ● ∣ V-● ∣ μ₁
    → μ₁ ∣ pc ⊢ M       ⇓ₑ V ∣ v   ∣ μ₂
      ---------------------------------------- Application●
    → μ  ∣ pc ⊢ L · M   ⇓ₑ ● ∣ V-● ∣ μ₂

  ⇓ₑ-if-true : ∀ {μ μ₁ μ₂ pc L M N V v A}
    → μ  ∣ pc ⊢ L ⇓ₑ $ true of low ∣ V-const ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
      ------------------------------------------------ IfTrue
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ v ∣ μ₂

  ⇓ₑ-if-false : ∀ {μ μ₁ μ₂ pc L M N V v A}
    → μ  ∣ pc ⊢ L ⇓ₑ $ false of low ∣ V-const ∣ μ₁
    → μ₁ ∣ pc ⊢ N ⇓ₑ V ∣ v ∣ μ₂
      ------------------------------------------------ IfFalse
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ v ∣ μ₂

  ⇓ₑ-if-● : ∀ {μ μ₁ pc L M N A}
    → μ  ∣ pc ⊢ L          ⇓ₑ ● ∣ V-● ∣ μ₁
      ------------------------------------------------ If●
    → μ  ∣ pc ⊢ if L A M N ⇓ₑ ● ∣ V-● ∣ μ₁

  ⇓ₑ-let : ∀ {μ μ₁ μ₂ pc M N V W v w}
    → μ  ∣ pc ⊢ M        ⇓ₑ V ∣ v ∣ μ₁
    → μ₁ ∣ pc ⊢ N [ V ]  ⇓ₑ W ∣ w ∣ μ₂
      ----------------------------------------- Let
    → μ  ∣ pc ⊢ `let M N ⇓ₑ W ∣ w ∣ μ₂

  ⇓ₑ-ref? : ∀ {μ μ₁ pc M V v n}
    → μ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₁
    → n ≡ length μ₁
    → pc ≼ low
      -------------------------------------------------------------------------------------- RefNSU
    → μ ∣ pc ⊢ ref?[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ ⟨ n , V , v ⟩ ∷ μ₁

  ⇓ₑ-ref : ∀ {μ μ₁ pc M V v n}
    → μ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₁
    → n ≡ length μ₁
      -------------------------------------------------------------------------------------- Ref
    → μ ∣ pc ⊢ ref[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ ⟨ n , V , v ⟩ ∷ μ₁

  ⇓ₑ-deref : ∀ {μ μ₁ pc M V v n}
    → μ ∣ pc ⊢ M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → find _≟_ μ₁ n ≡ just ⟨ V , v ⟩
      ---------------------------------- Deref
    → μ ∣ pc ⊢ ! M ⇓ₑ V ∣ v ∣ μ₁

  ⇓ₑ-deref-● : ∀ {μ μ₁ pc M}
    → μ ∣ pc ⊢ M   ⇓ₑ ● ∣ V-● ∣ μ₁
      ----------------------------------------- Deref●
    → μ ∣ pc ⊢ ! M ⇓ₑ ● ∣ V-● ∣ μ₁

  ⇓ₑ-assign? : ∀ {μ μ₁ μ₂ pc L M V v n}
    → μ  ∣ pc ⊢ L ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
    → pc ≼ low
      -------------------------------------------------------------------------- AssignNSU
    → μ ∣ pc ⊢ L :=? M ⇓ₑ $ tt of low ∣ V-const ∣ ⟨ n , V , v ⟩ ∷ μ₂

  ⇓ₑ-assign?-● : ∀ {μ μ₁ μ₂ pc L M V v}
    → μ  ∣ pc ⊢ L ⇓ₑ ● ∣ V-● ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v   ∣ μ₂
      -------------------------------------------------------- AssignNSU●
    → μ  ∣ pc ⊢ L :=? M ⇓ₑ $ tt of low ∣ V-const ∣ μ₂ {- skip assignment -}

  ⇓ₑ-assign : ∀ {μ μ₁ μ₂ pc L M V v n}
    → μ  ∣ pc ⊢ L ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
      -------------------------------------------------------------------------- Assign
    → μ  ∣ pc ⊢ L := M ⇓ₑ $ tt of low ∣ V-const ∣ ⟨ n , V , v ⟩ ∷ μ₂

  ⇓ₑ-assign-● : ∀ {μ μ₁ μ₂ pc L M V v}
    → μ  ∣ pc ⊢ L ⇓ₑ ● ∣ V-● ∣ μ₁
    → μ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v   ∣ μ₂
      -------------------------------------------------------- Assign●
    → μ  ∣ pc ⊢ L := M ⇓ₑ $ tt of low ∣ V-const ∣ μ₂ {- skip assignment -}
