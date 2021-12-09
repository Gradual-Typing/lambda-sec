module Types where

open import Data.Bool using (Bool) renaming (_≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.List using (List)
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
infix 7  _of_

data RawType where
  `_      : Base → RawType
  Ref_    : Type → RawType
  [_]_⇒_ : Label → Type → Type → RawType

data Type where
  _of_ : RawType → Label → Type

{- Type examples: -}
_ : Type
_ =  ([ ⋆ ] ` 𝔹 of ⋆ ⇒ ` 𝔹 of l high ) of l low

_ : Type
_ = Ref (` Unit of ⋆ ) of l high

{- Subtyping -}
infix 5 _≼_
infix 5 _<:ₗ_
infix 5 _<:ᵣ_
infix 5 _<:_

data _≼_ : StaticLabel → StaticLabel → Set where
  l⊑l : low  ≼ low
  l⊑h : low  ≼ high
  h⊑h : high ≼ high

data _<:ₗ_ : Label → Label → Set where
  <:-⋆ : ⋆ <:ₗ ⋆      {- neutral -}
  <:-l : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≼ ℓ₂ → l ℓ₁ <:ₗ l ℓ₂

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
  <:-ty : ∀ {g₁ g₂} {X Y}
    → g₁ <:ₗ g₂
    → X  <:ᵣ Y
      ---------------------
    → X of g₁ <: Y of g₂

{- Consistency -}
infix 5 _~ₗ_
infix 5 _~ᵣ_
infix 5 _~_

data _~ₗ_ : Label → Label → Set where
  ⋆~  : ∀ {g} → ⋆ ~ₗ g
  ~⋆  : ∀ {g} → g ~ₗ ⋆
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
  ~-ty : ∀ {g₁ g₂} {S T}
    → g₁ ~ₗ g₂
    → S  ~ᵣ T
      --------------------
    → S of g₁ ~ T of g₂

{- Consistent subtyping -}
infix 5 _≾_  -- of labels
infix 5 _≲ᵣ_ -- of raw types
infix 5 _≲_  -- of types

data _≾_ : Label → Label → Set where
  ≾-⋆r : ∀ {g} → g ≾ ⋆
  ≾-⋆l : ∀ {g} → ⋆ ≾ g
  ≾-l  : ∀ {ℓ₁ ℓ₂} → ℓ₁ ≼ ℓ₂ → l ℓ₁ ≾ l ℓ₂

data _≲ᵣ_ : RawType → RawType → Set
data _≲_  : Type → Type → Set

data _≲ᵣ_ where
  ≲-ι : ∀ {ι} → ` ι ≲ᵣ ` ι

  ≲-ref : ∀ {A B}
    → A ≲ B
    → B ≲ A
      -----------------
    → Ref A ≲ᵣ Ref B

  ≲-fun : ∀ {pc₁ pc₂} {A B C D}
    → pc₂ ≾ pc₁
    → C ≲ A
    → B ≲ D
      -----------------------------------
    → [ pc₁ ] A ⇒ B ≲ᵣ [ pc₂ ] C ⇒ D

data _≲_ where
  ≲-ty : ∀ {g₁ g₂} {S T}
    → g₁ ≾ g₂
    → S ≲ᵣ T
      --------------------
    → S of g₁ ≲ T of g₂

{- Label join -}
_⋎_ : StaticLabel → StaticLabel → StaticLabel
low ⋎ low = low
_   ⋎ _   = high

{- Label meet -}
_⋏_ : StaticLabel → StaticLabel → StaticLabel
high ⋏ high = high
_    ⋏ _    = low

{- Label consistent join -}
_⋎̃_ : Label → Label → Label
l ℓ₁     ⋎̃ l ℓ₂   = l (ℓ₁ ⋎ ℓ₂)
l high   ⋎̃ ⋆      = l high
_        ⋎̃ ⋆      = ⋆
⋆        ⋎̃ l high = l high
⋆        ⋎̃ _      = ⋆

{- Stamping label on type -}
stamp : Type → Label → Type
stamp (T of g₁ ) g₂ = T of g₁ ⋎̃ g₂

{- Precision join -}
private
  ⨆ₗ : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → Label
  ⨆ᵣ : ∀ {S T} → S ~ᵣ T → RawType

⨆ : ∀ {A B} → A ~ B → Type

⨆ₗ {⋆} {g₂}        ⋆~  = g₂
⨆ₗ {g₁} {⋆}        ~⋆  = g₁
⨆ₗ {- both low  -} l~l = l low
⨆ₗ {- both high -} h~h = l high

⨆ᵣ {` ι} {` ι} ~-ι = ` ι
⨆ᵣ (~-ref A~B) = Ref (⨆ A~B)
⨆ᵣ (~-fun pc₁~pc₂ A~C B~D) = [ ⨆ₗ pc₁~pc₂ ] ⨆ A~C ⇒ ⨆ B~D

⨆ (~-ty g₁~g₂ S~T) = ⨆ᵣ S~T of ⨆ₗ g₁~g₂

Context = List Type
