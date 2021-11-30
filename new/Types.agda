module Types where

open import Data.Bool using (Bool) renaming (_≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)

data Label : Set where
  * : Label
  ᴴ : Label
  ᴸ : Label

data StaticLabel : Label → Set where
  ᴴ : StaticLabel ᴴ
  ᴸ : StaticLabel ᴸ

data Base : Set where
  𝔹 : Base
  Unit : Base

rep : Base → Set
rep 𝔹 = Bool
rep Unit = ⊤

data RawType : Set
data Type : Set

infix 10 `_
infix 7  _[_]→_
infix 6  _^_

data RawType where
  `_      : Base → RawType
  Ref_    : Type → RawType
  _[_]→_ : Type → Label → Type → RawType

data Type where
  _^_ : RawType → Label → Type

{- Type examples: -}
_ : Type
_ = (` 𝔹 ^ *) [ ᴸ ]→ (` 𝔹 ^ ᴴ) ^ ᴸ

_ : Type
_ = Ref (` Unit ^ *) ^ ᴴ
