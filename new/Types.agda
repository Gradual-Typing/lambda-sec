module Types where

open import Data.Bool using (Bool) renaming (_≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

data StaticLabel : Set where
  high : StaticLabel
  low  : StaticLabel

data Label : Set where
  ⋆ : Label
  l : StaticLabel → Label

data Base : Set where
  𝔹 : Base
  Unit : Base

rep : Base → Set
rep 𝔹 = Bool
rep Unit = ⊤

data RawType : Set
data Type : Set

infix 10 `_
infix 6  [_]_⇒_
infix 7  _₍_₎

data RawType where
  `_      : Base → RawType
  Ref_    : Type → RawType
  [_]_⇒_ : Label → Type → Type → RawType

data Type where
  _₍_₎ : RawType → Label → Type

{- Type examples: -}
_ : Type
_ =  ([ ⋆ ] ` 𝔹 ₍ ⋆ ₎ ⇒ ` 𝔹 ₍ l high ₎) ₍ l low ₎

_ : Type
_ = Ref (` Unit ₍ ⋆ ₎) ₍ l high ₎

{- Subtyping -}
infix 5 _⊑_
infix 5 _<:ₗ_
infix 5 _<:ᵣ_
infix 5 _<:_

data _⊑_ : StaticLabel → StaticLabel → Set where
  l⊑l : low ⊑ low
  l⊑h : low ⊑ high
  h⊑h : high ⊑ high

data _<:ₗ_ : Label → Label → Set where
  <:-⋆ : ⋆ <:ₗ ⋆      {- neutral -}
  <:-l : ∀ {ℓ₁ ℓ₂} → ℓ₁ ⊑ ℓ₂ → l ℓ₁ <:ₗ l ℓ₂

data _<:ᵣ_ : RawType → RawType → Set
data _<:_ :  Type → Type → Set

data _<:ᵣ_ where
  <:-ι : ∀ {ι} → ` ι <:ᵣ ` ι

  <:-ref : ∀ {A B}
    → A <: B
    → B <: A
      ----------------
    → Ref A <:ᵣ Ref B

  <:-fun : ∀ {pc₁ pc₂} {A B C D}
    → pc₂ <:ₗ pc₁
    → C <: A
    → B <: D
      ----------------------------------
    → [ pc₁ ] A ⇒ B <:ᵣ [ pc₂ ] C ⇒ D

data _<:_ where
  <:-ty : ∀ {γ₁ γ₂} {X Y}
    → γ₁ <:ₗ γ₂
    → X  <:ᵣ Y
      ---------------------
    → X ₍ γ₁ ₎ <: Y ₍ γ₂ ₎

{- Consistency -}
infix 5 _~ₗ_
infix 5 _~ᵣ_
infix 5 _~_

data _~ₗ_ : Label → Label → Set where
  ⋆~  : ∀ {γ} → ⋆ ~ₗ γ
  ~⋆  : ∀ {γ} → γ ~ₗ ⋆
  l~l : l low ~ₗ l low
  h~h : l high ~ₗ l high

data _~ᵣ_ : RawType → RawType → Set
data _~_  : Type → Type → Set

data _~ᵣ_ where
  ~-ι : ∀ {ι} → ` ι ~ᵣ ` ι

  ~-ref : ∀ {A B}
    → A ~ B
      ---------------
    → Ref A ~ᵣ Ref B

  ~-fun : ∀ {pc₁ pc₂} {A B C D}
    → pc₁ ~ₗ pc₂
    → A ~ C
    → B ~ D
      ---------------------------------
    → [ pc₁ ] A ⇒ B ~ᵣ [ pc₂ ] C ⇒ D

data _~_ where
  ~-ty : ∀ {γ₁ γ₂} {S T}
    → γ₁ ~ₗ γ₂
    → S  ~ᵣ T
      --------------------
    → S ₍ γ₁ ₎ ~ T ₍ γ₂ ₎

{- Label join -}
_⋎_ : StaticLabel → StaticLabel → StaticLabel
low ⋎ low = low
_   ⋎ _   = high

{- Label meet -}
_⋏_ : StaticLabel → StaticLabel → StaticLabel
high ⋏ high = high
_    ⋏ _    = low

{- Label consistent join -}
infix 5 _⋎̃_

_⋎̃_ : Label → Label → Label
l ℓ₁     ⋎̃ l ℓ₂   = l (ℓ₁ ⋎ ℓ₂)
l high   ⋎̃ ⋆      = l high
_        ⋎̃ ⋆      = ⋆
⋆        ⋎̃ l high = l high
⋆        ⋎̃ _      = ⋆

⨆ : ∀ {A B} → A ~ B → Type
⨆ A~B = {!!}
