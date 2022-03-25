open import Types

module CCSyntax (Cast_⇒_ : Type → Type → Set) where

open import Data.List
open import Data.Bool renaming (Bool to 𝔹)

open import Syntax
open import BlameLabels
open import Addr


data Err : Set where
  blame   : BlameLabel → Err
  nsu-err : Err

data Op : Set where
  op-addr   : (a : Addr) → (ℓ : StaticLabel) → Op
  op-lam    : (pc : StaticLabel) → Type → (ℓ : StaticLabel) → Op
  op-app    : Op
  op-const  : ∀ {ι} → rep ι → StaticLabel → Op
  op-if     : Op
  op-let    : Op
  op-ref    : StaticLabel → Op
  op-deref  : Op
  op-assign : Op
  op-cast   : ∀ {A B} → Cast A ⇒ B → Op
  op-nsu-ref : StaticLabel → Op
  op-nsu-assign : Op
  op-prot   : StaticLabel → Op
  op-err    : Err → Op

sig : Op → List Sig
sig (op-addr a ℓ)      = []
sig (op-lam pc A ℓ)    = (ν ■) ∷ []
sig op-app             = ■ ∷ ■ ∷ []
sig (op-const k ℓ)     = []
sig op-if              = ■ ∷ ■ ∷ ■ ∷ []
sig op-let             = ■ ∷ (ν ■) ∷ []
sig (op-ref ℓ)         = ■ ∷ []
sig op-deref           = ■ ∷ []
sig op-assign          = ■ ∷ ■ ∷ []
sig (op-cast c)        = ■ ∷ []
sig (op-nsu-ref ℓ)     = ■ ∷ []
sig op-nsu-assign      = ■ ∷ ■ ∷ []
sig (op-prot ℓ)        = ■ ∷ []
sig (op-err e)         = []

open Syntax.OpSig Op sig renaming (ABT to Term) hiding (plug) public

infixl 7  _·_
infix 8 _⟨_⟩

pattern addr_of_ a ℓ             = (op-addr a ℓ) ⦅ nil ⦆
pattern ƛ[_]_˙_of_ pc A N ℓ      = (op-lam pc A ℓ) ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ L M                  = op-app ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern $_of_ k ℓ                = (op-const k ℓ) ⦅ nil ⦆
pattern if_then_else_endif L M N = op-if ⦅ cons (ast L) (cons (ast M) (cons (ast N) nil)) ⦆
pattern `let M N                 = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern ref[_]_ ℓ M              = (op-ref ℓ) ⦅ cons (ast M) nil ⦆
pattern !_ M                     = op-deref ⦅ cons (ast M) nil ⦆
pattern _:=_ L M                 = op-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern _⟨_⟩ M c                 = (op-cast c) ⦅ cons (ast M) nil ⦆
pattern nsu-ref ℓ M              = (op-nsu-ref ℓ) ⦅ cons (ast M) nil ⦆
pattern nsu-assign L M           = op-nsu-assign ⦅ cons (ast L) (cons (ast M) nil) ⦆
pattern prot[_]_ ℓ M             = (op-prot ℓ) ⦅ cons (ast M) nil ⦆ {- protection term -}
pattern err e                    = (op-err e) ⦅ nil ⦆               {- blame / nsu error -}
