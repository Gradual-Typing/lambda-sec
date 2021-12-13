open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import Types

module SurfaceSyntax where

data Op : Set where
  op-lam    : (pc : Label) → Type → (ℓ : StaticLabel) → Op
  op-app    : Op
  -- op-input  : StaticLabel → Op
  op-const  : ∀ {ι} → rep ι → StaticLabel → Op
  op-if     : Op
  op-ann    : Type → Op
  op-ref    : Type → Op
  op-deref  : Op
  op-assign : Op

sig : Op → List Sig
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
-- sig (op-input ℓ)       = []
sig (op-const k ℓ)     = []
sig op-if              = ■ ∷ ■ ∷ ■ ∷ []
sig (op-ann A)         = ■ ∷ []
sig (op-ref A)         = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign          = ■ ∷ ■ ∷ []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_

pattern ƛ[_]_˙_of_ pc A N ℓ = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
-- pattern input-of_ ℓ = (op-input ℓ) ⦅ nil ⦆
pattern $_of_ k ℓ = (op-const k ℓ) ⦅ nil ⦆
pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern _꞉_ M A = (op-ann A) ⦅ cons (ast M) nil ⦆
pattern ref A M = (op-ref A) ⦅ cons (ast M) nil ⦆
pattern !_ M = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_ L M = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆

_ : Term
_ = ((ƛ[ ⋆ ] (` Bool of ⋆ ) ˙ (` 0) of high) · (` 0))
