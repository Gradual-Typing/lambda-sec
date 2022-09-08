module HeapSecure where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst; subst₂)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC
open import BigStep
open import Erasure

heap-relate : ∀ {Σ gc pc A M V μ μ′}
  → [] ; Σ ; gc ; pc ⊢ M ⦂ A
  → μ ∣ high ⊢ M ⇓ V ∣ μ′
  → erase-μ μ ≡ erase-μ μ′
