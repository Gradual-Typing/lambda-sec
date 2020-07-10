module Statics where

open import Data.List using (List; []; _∷_)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Machine




infix 4 _[_]⊢_⦂_  -- Γ [ pc ]⊢ M ⦂ s

data _[_]⊢_⦂_ : Context → ℒ → Term → 𝕊 → Set where

  -- VAR:
  ⊢` : ∀ {Γ x t 𝓁 pc}
    → nth Γ x ≡ just (t / 𝓁)
    → pc ⊑ 𝓁  -- introduces pc
      ------------------
    → Γ [ pc ]⊢ ` x ⦂ (t / 𝓁)

  -- FUN:
  ⊢ƛ : ∀ {Γ N s₁ s₂ 𝓁 pc pc′}
    → (s₁ ∷ ([ pc ] s₁ ⇒ s₂) / 𝓁 ∷ Γ) [ pc ]⊢ N ⦂ s₂
    → pc′ ⊑ 𝓁
      ------------------------------------------
    → Γ [ pc′ ]⊢ ƛ[ pc ] N `/ 𝓁 ⦂ ([ pc ] s₁ ⇒ s₂) / 𝓁

  -- TRUE:
  ⊢true : ∀ {Γ 𝓁 pc}
    → pc ⊑ 𝓁
      -------------------------
    → Γ [ pc ]⊢ `true `/ 𝓁 ⦂ `𝔹 / 𝓁

  -- FALSE:
  ⊢false : ∀ {Γ 𝓁 pc}
    → pc ⊑ 𝓁
      -------------------------
    → Γ [ pc ]⊢ `false `/ 𝓁 ⦂ `𝔹 / 𝓁

  -- UNIT:
  ⊢unit : ∀ {Γ 𝓁 pc}
    → pc ⊑ 𝓁
      -------------------------
    → Γ [ pc ]⊢ `⟨⟩ `/ 𝓁 ⦂ `⊤ / 𝓁

  -- LOC:
  ⊢mem : ∀ {Γ n s 𝓁 pc}
    → pc ⊑ 𝓁
      --------------------------------------
    → Γ [ pc ]⊢ (mem n s) `/ 𝓁 ⦂ (s ref) / 𝓁

  -- APP:
  ⊢· : ∀ {Γ L M s₁ s₂ 𝓁 pc pc′}
    → Γ [ pc ]⊢ L ⦂ ([ pc′ ] s₁ ⇒ s₂) / 𝓁
    → Γ [ pc ]⊢ M ⦂ s₁
    → (pc ⊔ 𝓁) ⊑ pc′
      ------------------------------------
    → Γ [ pc ]⊢ L · M ⦂ s₂ ⊔ₛ 𝓁

  -- AND:
  ⊢∧ : ∀ {Γ M N 𝓁 pc}
    → Γ [ pc ]⊢ M ⦂ `𝔹 / 𝓁
    → Γ [ pc ]⊢ N ⦂ `𝔹 / 𝓁
      ---------------------------
    → Γ [ pc ]⊢ M `∧ N ⦂ `𝔹 / 𝓁

  -- OR:
  ⊢∨ : ∀ {Γ M N 𝓁 pc}
    → Γ [ pc ]⊢ M ⦂ `𝔹 / 𝓁
    → Γ [ pc ]⊢ N ⦂ `𝔹 / 𝓁
      --------------------------
    → Γ [ pc ]⊢ M `∨ N ⦂ `𝔹 / 𝓁

  -- REF:
  ⊢ref : ∀ {Γ M s pc}
    → Γ [ pc ]⊢ M ⦂ s
      -------------------------------------
    → Γ [ pc ]⊢ `ref[ s ] M ⦂ (s ref) / pc

  -- DEREF:
  ⊢deref : ∀ {Γ M s 𝓁 pc}
    → Γ [ pc ]⊢ M ⦂ (s ref) / 𝓁
      -------------------------
    → Γ [ pc ]⊢ ! M ⦂ s ⊔ₛ 𝓁

  -- ASSIGN:
  ⊢:= : ∀ {Γ L M t 𝓁 𝓁′ pc}
    → Γ [ pc ]⊢ L ⦂ ((t / 𝓁) ref) / 𝓁′
    → Γ [ pc ]⊢ M ⦂ t / 𝓁
    → 𝓁′ ⊑ 𝓁
      --------------------------
    → Γ [ pc ]⊢ L := M ⦂ `⊤ / pc

  -- COND:
  ⊢if : ∀ {Γ L M N s 𝓁 pc}
    → Γ [ pc ]⊢ L ⦂ `𝔹 / 𝓁
    → Γ [ pc ⊔ 𝓁 ]⊢ M ⦂ s
    → Γ [ pc ⊔ 𝓁 ]⊢ N ⦂ s
      ---------------------
    → Γ [ pc ]⊢ if L M N ⦂ s

  -- SUB:
  ⊢sub : ∀ {Γ M s s′ pc}
    → Γ [ pc ]⊢ M ⦂ s
    → s <:ₛ s′
      ---------------
    → Γ [ pc ]⊢ M ⦂ s′
