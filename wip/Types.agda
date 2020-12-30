module Types where

open import Data.Bool using (Bool) renaming (_≟_ to _≟ᵇ_)
open import Data.Nat using (ℕ) renaming (_≟_ to _≟ₙ_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)

data Prim : Set where
  `ℕ : Prim
  `𝔹 : Prim
  Unit : Prim
  Void : Prim

rep : Prim → Set
rep `ℕ = ℕ
rep `𝔹 = Bool
rep Unit = ⊤
rep Void = ⊥

data Label : Set where
  ᴴ : Label
  ᴸ : Label

data BlameLabel : Set where
  pos : ℕ → BlameLabel
  neg : ℕ → BlameLabel

data RawType : Set
data Type : Set

infix 10 `_
infix 7  _⟦_⟧⇒_
infix 6  _/_

data RawType where
  `_ : Prim → RawType
  _⟦_⟧⇒_ : Type → Label → Type → RawType
  Ref : Type → RawType

data Type where
  _/_ : RawType → Label → Type

-- Examples:
_ : Type
_ = (` `ℕ / ᴴ) ⟦ ᴸ ⟧⇒ (` `𝔹 / ᴴ) / ᴸ

_ : Type
_ = Ref (` Void / ᴸ) / ᴴ
