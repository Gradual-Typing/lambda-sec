module WFAddr where

open import Data.Nat
open import Data.List
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Reduction
open import Utils


WFAddr : HeapContext → Heap → Set
WFAddr Σ μ = ∀ a {V ℓ} → key _≟_ μ a ≡ just ⟨ V , ℓ ⟩ → a < length Σ
