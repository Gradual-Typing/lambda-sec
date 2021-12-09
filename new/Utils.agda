module Utils where

open import Data.List
open import Data.Maybe
open import Data.Nat

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ ls) zero    = just x
nth (x ∷ ls) (suc k) = nth ls k
