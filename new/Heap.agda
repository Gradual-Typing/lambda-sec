module Heap where

open import Types

open import Data.Nat
open import Data.List using (List)
open import Data.Product using (_×_)

Loc = ℕ

{- Loc ↦ Type -}
HeapContext = List (Loc × Type)
