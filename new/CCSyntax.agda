open import Types

module CCSyntax (Cast_⇒_ : Type → Type → Set) where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import Addr


data Op : Set where
  op-addr   : (a : Addr) → Op
  op-lam    : (pc : Label) → Type → (ℓ : StaticLabel) → Op
  op-app    : Op
  op-const  : ∀ {ι} → rep ι → StaticLabel → Op
  op-if     : Op
  op-ref    : Type → Op
  op-deref  : Op
  op-assign : Op
  op-cast   : ∀ {A B} → Cast A ⇒ B → Op

sig : Op → List Sig
sig (op-addr a)        = []
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig op-if              = ■ ∷ ■ ∷ ■ ∷ []
sig (op-ref A)         = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign          = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_

pattern addr a = (op-addr a) ⦅ nil ⦆
pattern ƛ[_]_˙_of_ pc A N ℓ = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ = (op-const k ℓ) ⦅ nil ⦆
pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ref A M = (op-ref A) ⦅ cons (ast M) nil ⦆
pattern !_ M = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_ L M = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c = (op-cast c) ⦅ cons (ast M) nil ⦆
