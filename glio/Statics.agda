module Statics where

open import Data.List using (List; []; _∷_)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Machine




infix 4 _[_]⊢_⦂_  -- Γ [ pc ]⊢ M ⦂ s

data _[_]⊢_⦂_ : Context → ℒ → Term → 𝕊 → Set where

  -- VAR:
  ⊢` : ∀ {Γ x t ℓ pc}
    → nth Γ x ≡ just (t / ℓ)
    → pc ⊑ ℓ  -- introduces pc
      ------------------
    → Γ [ pc ]⊢ ` x ⦂ (t / ℓ)

  -- FUN:
  ⊢ƛ : ∀ {Γ N s₁ s₂ ℓ pc pc′}
    → (s₁ ∷ ([ pc ] s₁ ⇒ s₂) / ℓ ∷ Γ) [ pc ]⊢ N ⦂ s₂
    → pc′ ⊑ ℓ
      ------------------------------------------
    → Γ [ pc′ ]⊢ ƛ[ pc ] N `/ ℓ ⦂ ([ pc ] s₁ ⇒ s₂) / ℓ

  -- TRUE:
  ⊢true : ∀ {Γ ℓ pc}
    → pc ⊑ ℓ
      -------------------------
    → Γ [ pc ]⊢ `true `/ ℓ ⦂ `𝔹 / ℓ

  -- FALSE:
  ⊢false : ∀ {Γ ℓ pc}
    → pc ⊑ ℓ
      -------------------------
    → Γ [ pc ]⊢ `false `/ ℓ ⦂ `𝔹 / ℓ

  -- UNIT:
  ⊢unit : ∀ {Γ ℓ pc}
    → pc ⊑ ℓ
      -------------------------
    → Γ [ pc ]⊢ `⟨⟩ `/ ℓ ⦂ `⊤ / ℓ

  -- LOC:
  ⊢mem : ∀ {Γ n s ℓ pc}
    → pc ⊑ ℓ
      --------------------------------------
    → Γ [ pc ]⊢ (mem n s) `/ ℓ ⦂ (s ref) / ℓ

  -- APP:
  ⊢· : ∀ {Γ L M s₁ s₂ ℓ pc pc′}
    → Γ [ pc ]⊢ L ⦂ ([ pc′ ] s₁ ⇒ s₂) / ℓ
    → Γ [ pc ]⊢ M ⦂ s₁
    → (pc ⊔ ℓ) ⊑ pc′
      ------------------------------------
    → Γ [ pc ]⊢ L · M ⦂ s₂ ⊔ₛ ℓ

  -- AND:
  ⊢∧ : ∀ {Γ M N ℓ pc}
    → Γ [ pc ]⊢ M ⦂ `𝔹 / ℓ
    → Γ [ pc ]⊢ N ⦂ `𝔹 / ℓ
      ---------------------------
    → Γ [ pc ]⊢ M `∧ N ⦂ `𝔹 / ℓ

  -- OR:
  ⊢∨ : ∀ {Γ M N ℓ pc}
    → Γ [ pc ]⊢ M ⦂ `𝔹 / ℓ
    → Γ [ pc ]⊢ N ⦂ `𝔹 / ℓ
      --------------------------
    → Γ [ pc ]⊢ M `∨ N ⦂ `𝔹 / ℓ

  -- REF:
  ⊢ref : ∀ {Γ M s pc}
    → Γ [ pc ]⊢ M ⦂ s
      -------------------------------------
    → Γ [ pc ]⊢ `ref[ s ] M ⦂ (s ref) / pc

  -- DEREF:
  ⊢deref : ∀ {Γ M s ℓ pc}
    → Γ [ pc ]⊢ M ⦂ (s ref) / ℓ
      -------------------------
    → Γ [ pc ]⊢ ! M ⦂ s ⊔ₛ ℓ

  -- ASSIGN:
  ⊢:= : ∀ {Γ L M t ℓ ℓ′ pc}
    → Γ [ pc ]⊢ L ⦂ ((t / ℓ) ref) / ℓ′
    → Γ [ pc ]⊢ M ⦂ t / ℓ
    → ℓ′ ⊑ ℓ
      --------------------------
    → Γ [ pc ]⊢ L := M ⦂ `⊤ / pc

  -- COND:
  ⊢if : ∀ {Γ L M N s ℓ pc}
    → Γ [ pc ]⊢ L ⦂ `𝔹 / ℓ
    → Γ [ pc ⊔ ℓ ]⊢ M ⦂ s
    → Γ [ pc ⊔ ℓ ]⊢ N ⦂ s
      ---------------------
    → Γ [ pc ]⊢ if L M N ⦂ s

  -- SUB:
  ⊢sub : ∀ {Γ M s s′ pc}
    → Γ [ pc ]⊢ M ⦂ s
    → s <:ₛ s′
      ---------------
    → Γ [ pc ]⊢ M ⦂ s′
