module Machine where

import Syntax
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)



-- Types:
infixr 6 [_]_⇒_
infix  6 _ref
infix  7 _/_
-- Terms:
infix  4 `ref[_]_
infix  5 ƛ[_]_
infix  6 _`/_
infixl 7 _·_
infixl 8 _`∧_
infixl 8 _`∨_
infixr 9 _:=_   -- Assignment is right associative.

data ℒ : Set where
  label : ℕ → ℒ

-- Examples: low and high.
𝐿 : ℒ
𝐿 = label 0

𝐻 : ℒ
𝐻 = label 1

mutual
  -- Types
  data 𝕋 : Set where
    [_]_⇒_   : ℒ → 𝕊 → 𝕊 → 𝕋
    `𝔹      : 𝕋
    `⊤       : 𝕋
    _ref     : 𝕊 → 𝕋

  -- Security types: types with label snapped on
  data 𝕊 : Set where
    _/_ : 𝕋 → ℒ → 𝕊

-- A few auxiliary definitions / lemmas about labels and types
-- least upper bound / join:
_⊔_ : ℒ → ℒ → ℒ
(label n) ⊔ (label n′) = label (n ⊔ₙ n′)

-- label stamping
_⊔ₛ_ : 𝕊 → ℒ → 𝕊
(s / 𝓁₁) ⊔ₛ 𝓁₂ = s / (𝓁₁ ⊔ 𝓁₂)

-- partial ordering of labels
data _⊑_ : ℒ → ℒ → Set where

  ⊑-l : ∀ {n , n′ : ℕ}
      → n ≤ n′
      → (label n) ⊑ (label n′)

𝐿⊑𝐻 : 𝐿 ⊑ 𝐻
𝐿⊑𝐻 = ⊑-l {0} {1} z≤n

⊑-refl : ∀ {𝓁} → 𝓁 ⊑ 𝓁
⊑-refl {label n} = ⊑-l {n} {n} ≤-refl

≤-dec : (n : ℕ) → (n′ : ℕ) → Dec (n ≤ n′)
≤-dec zero zero = yes z≤n
≤-dec zero (suc n′) = yes z≤n
≤-dec (suc n) zero = no λ ()
≤-dec (suc n) (suc n′) with ≤-dec n n′
... | yes n≤n′ = yes (s≤s n≤n′)
... | no ¬n≤n′ = no λ {(s≤s n≤n′) → ¬n≤n′ n≤n′}

-- label comparison is decidable:
⊑-dec : (𝓁 : ℒ) → (𝓁′ : ℒ) → Dec (𝓁 ⊑ 𝓁′)
⊑-dec (label n) (label n′) with ≤-dec n n′
... | yes n≤n′ = yes (⊑-l {n} {n′} n≤n′)
... | no ¬n≤n′ = no λ {(⊑-l n≤n′) → ¬n≤n′ n≤n′ }

-- Algorithmic subtyping:
mutual
  data _<:ₜ_ : 𝕋 → 𝕋 → Set where

    <:-𝔹 : `𝔹 <:ₜ `𝔹

    <:-⊤ : `⊤ <:ₜ `⊤

    <:-ref : ∀ {s : 𝕊}
        -----------
      → (s ref) <:ₜ (s ref)   -- Note we require the types referenced to to be the same here

    <:-⇒ : ∀ {s₁′ s₁ s₂ s₂′ pc pc′}
      → pc′ ⊑ pc
      → s₁′ <:ₛ s₁
      → s₂  <:ₛ s₂′
        -----------
      → ([ pc ] s₁ ⇒ s₂) <:ₜ ([ pc′ ] s₁′ ⇒ s₂′)

  data _<:ₛ_ : 𝕊 → 𝕊 → Set where

    <:-lab : ∀ {t t′ 𝓁 𝓁′}
      → t <:ₜ t′
      → 𝓁 ⊑ 𝓁′
        ------------------
      → (t / 𝓁) <:ₛ (t′ / 𝓁′)

-- Typing context
Context : Set
Context = List 𝕊

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] k = nothing
nth (x ∷ ls) zero = just x
nth (x ∷ ls) (suc k) = nth ls k

data Op : Set where
  op-lam        : ℒ → Op        -- ƛ
  op-true       : Op
  op-false      : Op
  op-unit       : Op
  op-memory     : ℕ → 𝕊 → Op   -- memory reference
  op-app        : Op            -- ·
  op-if         : Op
  op-and        : Op            -- ∧
  op-or         : Op            -- ∨
  op-ref        : 𝕊 → Op        -- `refˢ
  op-deref      : Op            -- `deref
  op-assign     : Op            -- :=
  op-label      : ℒ → Op        -- / (label annotation)

sig : Op → List ℕ
sig (op-lam pc)        = 2 ∷ []   -- First we bind f then we bind x
sig op-true            = []
sig op-false           = []
sig op-unit            = []
sig (op-memory n s)    = []
sig op-app             = 0 ∷ 0 ∷ []
sig op-if              = 0 ∷ 0 ∷ 0 ∷ []
sig op-and             = 0 ∷ 0 ∷ []
sig op-or              = 0 ∷ 0 ∷ []
sig (op-ref s)         = 0 ∷ []
sig op-deref           = 0 ∷ []
sig op-assign          = 0 ∷ 0 ∷ []
sig (op-label 𝓁)       = 0 ∷ []

-- We're using the ABT library.
open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; Rename; ⟪_⟫; ⟦_⟧; exts; _•_; id; exts-sub-cons; sub-id)
  renaming (ABT to Term) public


pattern ƛ[_]_ pc N    = (op-lam pc) ⦅ cons (bind (bind (ast N))) nil ⦆                   -- ƛ[ pc ] N
pattern `true         = op-true ⦅ nil ⦆                                                  -- `true
pattern `false        = op-false ⦅ nil ⦆                                                 -- `false
pattern `⟨⟩           = op-unit ⦅ nil ⦆                                                  -- `⟨⟩
pattern mem n s       = (op-memory n s) ⦅ nil ⦆                                          -- mem n s
pattern _·_ L M       = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆                       -- L · M
pattern if L M N      = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆         -- if L M N
pattern _`∧_ M N      = op-and ⦅ cons (ast M) (cons (ast N) nil) ⦆                       -- M `∧ N
pattern _`∨_ M N      = op-or ⦅ cons (ast M) (cons (ast N) nil) ⦆                        -- M `∨ N
pattern `ref[_]_ s M  = (op-ref s) ⦅ cons (ast M) nil ⦆                                  -- `ref[ s ] M
pattern ! M           = op-deref ⦅ cons (ast M) nil ⦆                                    -- ! M
pattern _:=_ L M      = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆                    -- L := M
pattern _`/_ V 𝓁      = (op-label 𝓁) ⦅ cons (ast V) nil ⦆                                -- V `/ 𝓁

data Cell : Set where
  _↦_ : 𝕊 → Term → Cell

Memory : Set
Memory = List Cell
