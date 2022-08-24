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

infix 2 _∣_∣_⊢_⇓ₑ_∣_∣_

{- runs on erased terms -}
data _∣_∣_⊢_⇓ₑ_∣_∣_ : HalfHeap → HalfHeapContext → StaticLabel → Term → (V : Term) → Value V → HalfHeap → Set where

  ⇓ₑ-val : ∀ {μ Σ pc V v}
      --------------------------- Value
    → μ ∣ Σ ∣ pc ⊢ V ⇓ₑ V ∣ v ∣ μ

  ⇓ₑ-app : ∀ {μ μ₁ μ₂ μ₃ Σ Σ₁ Σ₂ pc pc′ L M N V W v w A}
    → μ  ∣ Σ  ∣ pc ⊢ L       ⇓ₑ ƛ[ pc′ ] A ˙ N of low ∣ V-ƛ ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ M       ⇓ₑ V ∣ v ∣ μ₂
    → μ₂ ∣ Σ₂ ∣ pc ⊢ N [ V ] ⇓ₑ W ∣ w ∣ μ₃
      ---------------------------------------- Application
    → μ  ∣ Σ  ∣ pc ⊢ L · M   ⇓ₑ W ∣ w ∣ μ₃

  ⇓ₑ-if-true : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M N V v A}
    → μ  ∣ Σ  ∣ pc ⊢ L ⇓ₑ $ true of low ∣ V-const ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
      ------------------------------------------------ IfTrue
    → μ  ∣ Σ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ v ∣ μ₂

  ⇓ₑ-if-false : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M N V v A}
    → μ  ∣ Σ  ∣ pc ⊢ L ⇓ₑ $ false of low ∣ V-const ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ N ⇓ₑ V ∣ v ∣ μ₂
      ------------------------------------------------ IfFalse
    → μ  ∣ Σ  ∣ pc ⊢ if L A M N ⇓ₑ V ∣ v ∣ μ₂

  ⇓ₑ-let : ∀ {μ μ₁ μ₂ Σ Σ₁ pc M N V W v w}
    → μ  ∣ Σ  ∣ pc ⊢ M        ⇓ₑ V ∣ v ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ N [ V ]  ⇓ₑ W ∣ w ∣ μ₂
      ----------------------------------------- Let
    → μ  ∣ Σ  ∣ pc ⊢ `let M N ⇓ₑ W ∣ w ∣ μ₂

  ⇓ₑ-ref? : ∀ {μ μ₁ Σ pc M V v n}
    → μ ∣ Σ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₁
    → n ≡ length Σ
    → pc ≼ low
      -------------------------------------------------------------------------------------- RefNSU
    → μ ∣ Σ ∣ pc ⊢ ref?[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ ⟨ n , V , v ⟩ ∷ μ₁

  ⇓ₑ-ref : ∀ {μ μ₁ Σ pc M V v n}
    → μ ∣ Σ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₁
    → n ≡ length Σ
      -------------------------------------------------------------------------------------- Ref
    → μ ∣ Σ ∣ pc ⊢ ref[ low ] M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ ⟨ n , V , v ⟩ ∷ μ₁

  ⇓ₑ-deref : ∀ {μ μ₁ Σ pc M V v n}
    → μ ∣ Σ ∣ pc ⊢ M ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → find _≟_ μ n ≡ just ⟨ V , v ⟩
      ---------------------------------- Deref
    → μ ∣ Σ ∣ pc ⊢ ! M ⇓ₑ V ∣ v ∣ μ₁

  ⇓ₑ-assign? : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V v n}
    → μ  ∣ Σ  ∣ pc ⊢ L ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
    → pc ≼ low
      -------------------------------------------------------------------------- AssignNSU
    → μ ∣ Σ ∣ pc ⊢ L :=? M ⇓ₑ $ tt of low ∣ V-const ∣ ⟨ n , V , v ⟩ ∷ μ₂

  ⇓ₑ-assign : ∀ {μ μ₁ μ₂ Σ Σ₁ pc L M V v n}
    → μ  ∣ Σ  ∣ pc ⊢ L ⇓ₑ addr (a[ low ] n) of low ∣ V-addr ∣ μ₁
    → μ₁ ∣ Σ₁ ∣ pc ⊢ M ⇓ₑ V ∣ v ∣ μ₂
      -------------------------------------------------------------------------- Assign
    → μ ∣ Σ ∣ pc ⊢ L := M ⇓ₑ $ tt of low ∣ V-const ∣ ⟨ n , V , v ⟩ ∷ μ₂
