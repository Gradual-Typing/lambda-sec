module BlameLabels where

open import Data.Nat using (ℕ)

data BlameLabel : Set where
  pos : ℕ → BlameLabel
  neg : ℕ → BlameLabel

flip : BlameLabel → BlameLabel
flip (pos n) = (neg n)
flip (neg n) = (pos n)
