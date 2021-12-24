open import Types

module CCSyntax (Cast_⇒_ : Type → Type → Set) where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import Addr


data Ensure : Set where
  static : Ensure
  dyn    : Ensure

data Op : Set where
  op-addr   : (a : Addr) → (ℓ : StaticLabel) → Op
  op-lam    : (pc : StaticLabel) → Type → (ℓ : StaticLabel) → Op
  op-app    : Op
  op-const  : ∀ {ι} → rep ι → StaticLabel → Op
  op-if     : Op
  op-ref    : StaticLabel → Ensure → Op
  op-deref  : Op
  op-assign : Ensure → Op
  op-cast   : ∀ {A B} → Cast A ⇒ B → Op

sig : Op → List Sig
sig (op-addr a ℓ)      = []
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig op-if              = ■ ∷ ■ ∷ ■ ∷ []
sig (op-ref ℓ e)       = ■ ∷ []
sig op-deref           = ■ ∷ []
sig (op-assign e)      = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_

pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ[_]_˙_of_ pc A N ℓ      = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M                  = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ref[_]_#_ ℓ M e          = (op-ref ℓ e) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_#_ L M e             = (op-assign e) ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c                 = (op-cast c) ⦅ cons (ast M) nil ⦆
