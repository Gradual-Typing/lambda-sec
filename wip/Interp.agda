module Interp where

open import Data.Product using (_×_; ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)

data Cell : Set where
  _,_↦_ : ℒ̂ → ℒ̂ → Term → Cell

Store : Set
Store = List Cell

Env : Set
Env = List Term

MachConf : Set
MachConf = Store × Term × ℒ̂

data Error : Set where
  castError : Error
  NSUError : Error
  storeOutofBound : Error

data Result (X : Set) : Set where
  error : Error → Result X
  result : X → Result X

𝒱 : Env → MachConf → Result MachConf
