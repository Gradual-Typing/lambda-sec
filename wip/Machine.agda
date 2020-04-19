module Machine where

import Syntax
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe


-- types
-- infixr 6 _⇒_
-- infix  7 _/_

infix  4 `ref[_]_
infix  5 ƛ[_]_
infix  6 _`/_
infixl 7 _·_
infixl 8 _`∧_
infixl 8 _`∨_
-- Assignment is right associative.
infixr 9 _:=_

data ℒ : Set where
  Label : ℕ → ℒ

-- Examples: low and high.
𝐿 : ℒ
𝐿 = Label 0

𝐻 : ℒ
𝐻 = Label 1

mutual
  -- types
  data 𝕋 : Set where
    _⇒_ : 𝕊 → 𝕊 → 𝕋
    `𝔹  : 𝕋

  -- security types: types with label snapped on
  data 𝕊 : Set where
    _/_ : 𝕋 → ℒ → 𝕊

-- typing context
Context : Set
Context = List 𝕊

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] k = nothing
nth (x ∷ ls) zero = just x
nth (x ∷ ls) (suc k) = nth ls k

data Op : Set where
  op-lam        : ℒ → Op    -- ƛ
  op-true       : Op
  op-false      : Op
  op-unit       : Op
  op-app        : Op        -- ·
  op-if         : Op
  op-and        : Op        -- ∧
  op-or         : Op        -- ∨
  op-ref        : 𝕊 → Op    -- `refˢ
  op-deref      : Op        -- `deref
  op-assign     : Op        -- :=
  op-label      : ℒ → Op    -- / (label annotation)
  -- TODO: memory location

sig : Op → List ℕ
sig (op-lam pc)        = 2 ∷ []
sig op-true            = []
sig op-false           = []
sig op-unit            = []
sig op-app             = 0 ∷ 0 ∷ []
sig op-if              = 0 ∷ 0 ∷ 0 ∷ []
sig op-and             = 0 ∷ 0 ∷ []
sig op-or              = 0 ∷ 0 ∷ []
sig (op-ref s)         = 0 ∷ []
sig op-deref           = 0 ∷ []
sig op-assign          = 0 ∷ 0 ∷ []
sig (op-label 𝓁)  = 0 ∷ []

-- We're using the ABT library.
open Syntax Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; Rename; ⟪_⟫; ⟦_⟧; exts; _•_; id; exts-sub-cons; sub-id)
  renaming (ABT to Term) public


pattern ƛ[_]_ pc N    = (op-lam pc) ⦅ cons (bind (bind (ast N))) nil ⦆                   -- ƛ[ pc ] N
pattern `true         = op-true ⦅ nil ⦆                                                  -- `true
pattern `false        = op-false ⦅ nil ⦆                                                 -- `false
pattern `⟨⟩           = op-unit ⦅ nil ⦆                                                  -- `⟨⟩
pattern _·_ L M       = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆                       -- L · M
pattern if L M N      = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆         -- if L M N
pattern _`∧_ M N      = op-and ⦅ cons (ast M) (cons (ast N) nil) ⦆                       -- M `∧ N
pattern _`∨_ M N      = op-or ⦅ cons (ast M) (cons (ast N) nil) ⦆                        -- M `∨ N
pattern `ref[_]_ s M  = (op-ref s) ⦅ cons (ast M) nil ⦆                                  -- `ref[ s ] M
pattern ! M           = op-deref ⦅ cons (ast M) nil ⦆                                    -- ! M
pattern _:=_ L M      = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆                    -- L := M
pattern _`/_ V 𝓁       = (op-label 𝓁) ⦅ cons (ast V) nil ⦆                               -- V `/ 𝓁

-- Memory is a map from location Lˢ to values.
-- data Memory : Set where
--   `∅ : Memory
--   _;_⦂_ : Memory → 𝕊 → Value → Memory
