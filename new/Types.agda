module Types where

open import Data.Maybe
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
  using (_≡_; _≢_; refl; trans; sym; subst; cong; cong₂)

open import Addr


data StaticLabel : Set where
  high : StaticLabel
  low  : StaticLabel

data Label : Set where
  ⋆ : Label
  l : StaticLabel → Label

data Base : Set where
  Bool : Base
  Unit : Base

rep : Base → Set
rep Bool = 𝔹
rep Unit = ⊤

data RawType : Set
data Type : Set

infix 10 `_
infix 8  [_]_⇒_
infix 7  _of_

data RawType where
  `_      : Base → RawType
  Ref_    : Type → RawType
  [_]_⇒_ : Label → Type → Type → RawType

data Type where
  _of_ : RawType → Label → Type

{- Type examples: -}
_ : Type
_ =  [ ⋆ ] (` Bool of ⋆) ⇒ (` Bool of l high) of l low

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

  <:-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₂ <:ₗ gc₁
    → C <: A
    → B <: D
      ----------------------------------
    → [ gc₁ ] A ⇒ B <:ᵣ [ gc₂ ] C ⇒ D

data _<:_ where
  <:-ty : ∀ {g₁ g₂} {S T}
    → g₁ <:ₗ g₂
    → S  <:ᵣ T
      ---------------------
    → S of g₁ <: T of g₂

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

  ~-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₁ ~ₗ gc₂
    → A ~ C
    → B ~ D
      ---------------------------------
    → [ gc₁ ] A ⇒ B ~ᵣ [ gc₂ ] C ⇒ D

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

  ≲-fun : ∀ {gc₁ gc₂} {A B C D}
    → gc₂ ≾ gc₁
    → C ≲ A
    → B ≲ D
      -----------------------------------
    → [ gc₁ ] A ⇒ B ≲ᵣ [ gc₂ ] C ⇒ D

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
-- l high   ⋎̃ ⋆      = l high
_        ⋎̃ ⋆      = ⋆
-- ⋆        ⋎̃ l high = l high
⋆        ⋎̃ _      = ⋆

{- Label consistent meet -}
_⋏̃_ : Label → Label → Label
l ℓ₁     ⋏̃ l ℓ₂   = l (ℓ₁ ⋏ ℓ₂)
-- l low    ⋏̃ ⋆      = l low
_        ⋏̃ ⋆      = ⋆
-- ⋆        ⋏̃ l low  = l low
⋆        ⋏̃ _      = ⋆

consis-join-~ₗ : ∀ {g₁ g₂ g}
  → g₁ ~ₗ g
  → g₂ ~ₗ g
  → g ~ₗ g₁ ⋎̃ g₂
consis-join-~ₗ ⋆~ ⋆~ = ~⋆
consis-join-~ₗ ⋆~ ~⋆ = ⋆~
consis-join-~ₗ ⋆~ l~l = ~⋆
consis-join-~ₗ ⋆~ h~h = ~⋆
consis-join-~ₗ ~⋆ _ = ⋆~
consis-join-~ₗ l~l ⋆~ = ~⋆
consis-join-~ₗ l~l l~l = l~l
consis-join-~ₗ h~h ⋆~ = ~⋆
consis-join-~ₗ h~h h~h = h~h

{- Stamping label on type -}
stamp : Type → Label → Type
stamp (T of g₁) g₂ = T of g₁ ⋎̃ g₂

{- Precision join -}
private
  ⨆ₗ : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → Label -- of labels
  ⨆ᵣ : ∀ {S T} → S ~ᵣ T → RawType   -- of raw types

⨆ : ∀ {A B} → A ~ B → Type          -- of types

⨆ₗ {⋆} {g}         ⋆~  = g
⨆ₗ {g} {⋆}         ~⋆  = g
⨆ₗ {- both low  -} l~l = l low
⨆ₗ {- both high -} h~h = l high

⨆ᵣ {` ι} {` ι} ~-ι = ` ι
⨆ᵣ (~-ref A~B) = Ref (⨆ A~B)
⨆ᵣ (~-fun gc₁~gc₂ A~C B~D) = [ ⨆ₗ gc₁~gc₂ ] ⨆ A~C ⇒ ⨆ B~D

⨆ (~-ty g₁~g₂ S~T) = ⨆ᵣ S~T of ⨆ₗ g₁~g₂

{- Gradual meet -}
infix 5 _⊓ₗ_
infix 5 _⊓ᵣ_
infix 5 _⊓_

_⊓ₗ_ : Label → Label → Maybe Label
l high ⊓ₗ l high = just (l high)
l low  ⊓ₗ l low  = just (l low)
⋆      ⊓ₗ g      = just g
g      ⊓ₗ ⋆      = just g
_      ⊓ₗ _      = nothing

_⊓ᵣ_ : RawType → RawType → Maybe RawType
_⊓_ : Type → Type → Maybe Type

` Unit ⊓ᵣ ` Unit = just (` Unit)
` Bool ⊓ᵣ ` Bool = just (` Bool)
Ref A ⊓ᵣ Ref B =
  do
    A⊓B ← A ⊓ B
    just (Ref A⊓B)
[ gc₁ ] A ⇒ B ⊓ᵣ [ gc₂ ] C ⇒ D =
  do
    gc₁⊓gc₂ ← gc₁ ⊓ₗ gc₂
    A⊓C ← A ⊓ C
    B⊓D ← B ⊓ D
    just ([ gc₁⊓gc₂ ] A⊓C ⇒ B⊓D)
_ ⊓ᵣ _ = nothing

S of g₁ ⊓ T of g₂ =
  do
    S⊓T   ← S ⊓ᵣ T
    g₁⊓g₂ ← g₁ ⊓ₗ g₂
    just (S⊓T of g₁⊓g₂)

{- Consistent join of types -}
infix 5 _∨̃ᵣ_
infix 5 _∨̃_
{- Consistent meet of types -}
infix 5 _∧̃ᵣ_
infix 5 _∧̃_

_∨̃ᵣ_ : RawType → RawType → Maybe RawType
_∧̃ᵣ_ : RawType → RawType → Maybe RawType
_∨̃_ : Type → Type → Maybe Type
_∧̃_ : Type → Type → Maybe Type

` Unit ∨̃ᵣ ` Unit = just (` Unit)
` Bool ∨̃ᵣ ` Bool = just (` Bool)
Ref A ∨̃ᵣ Ref B =
  do
  A⊓B ← A ⊓ B
  just (Ref A⊓B)
[ gc₁ ] A ⇒ B ∨̃ᵣ [ gc₂ ] C ⇒ D =
  do
    A∧̃C ← A ∧̃ C
    B∨̃D ← B ∨̃ D
    just ([ gc₁ ⋏̃ gc₂ ] A∧̃C ⇒ B∨̃D)
_ ∨̃ᵣ _ = nothing

` Unit ∧̃ᵣ ` Unit = just (` Unit)
` Bool ∧̃ᵣ ` Bool = just (` Bool)
Ref A ∧̃ᵣ Ref B =
  do
    A⊓B ← A ⊓ B
    just (Ref A⊓B)
[ gc₁ ] A ⇒ B ∧̃ᵣ [ gc₂ ] C ⇒ D =
  do
    A∨̃C ← A ∨̃ C
    B∧̃D ← B ∧̃ D
    just ([ gc₁ ⋎̃ gc₂ ] A∨̃C ⇒ B∧̃D)
_ ∧̃ᵣ _ = nothing

S of g₁ ∨̃ T of g₂ =
  do
    S∨̃T ← S ∨̃ᵣ T
    just (S∨̃T of g₁ ⋎̃ g₂)

S of g₁ ∧̃ T of g₂ =
  do
    S∧̃T ← S ∧̃ᵣ T
    just (S∧̃T of g₁ ⋏̃ g₂)

≼-refl : ∀ {ℓ} → ℓ ≼ ℓ
≼-refl {high}  = h⊑h
≼-refl {low}   = l⊑l

<:ₗ-refl : ∀ {g} → g <:ₗ g
<:ₗ-refl {⋆}   = <:-⋆
<:ₗ-refl {l ℓ} = <:-l ≼-refl

~ₗ-refl : ∀ {g} → g ~ₗ g
~ₗ-refl {⋆}      = ⋆~
~ₗ-refl {l high} = h~h
~ₗ-refl {l low}  = l~l

~ᵣ-refl : ∀ {T} → T ~ᵣ T
~-refl : ∀ {A} → A ~ A
~ᵣ-refl {` ι} = ~-ι
~ᵣ-refl {Ref A} = ~-ref ~-refl
~ᵣ-refl {[ gc ] A ⇒ B} = ~-fun ~ₗ-refl ~-refl ~-refl
~-refl {T of g} = ~-ty ~ₗ-refl ~ᵣ-refl

≾-refl : ∀ {g} → g ≾ g
≾-refl {⋆} = ≾-⋆r
≾-refl {l x} = ≾-l ≼-refl

≲ᵣ-refl : ∀ {T} → T ≲ᵣ T
≲-refl : ∀ {A} → A ≲ A

≲ᵣ-refl {` ι} = ≲-ι
≲ᵣ-refl {Ref A} = ≲-ref ≲-refl ≲-refl
≲ᵣ-refl {[ gc ] A ⇒ B} = ≲-fun ≾-refl ≲-refl ≲-refl

≲-refl {T of g} = ≲-ty ≾-refl ≲ᵣ-refl

<:ᵣ-refl : ∀ {T} → T <:ᵣ T
<:-refl : ∀ {A} → A <: A

<:ᵣ-refl {` ι} = <:-ι
<:ᵣ-refl {Ref A} = <:-ref <:-refl <:-refl
<:ᵣ-refl {[ gc ] A ⇒ B} = <:-fun <:ₗ-refl <:-refl <:-refl

<:-refl {T of g} = <:-ty <:ₗ-refl <:ᵣ-refl

≼-antisym : ∀ {ℓ₁ ℓ₂}
  → ℓ₁ ≼ ℓ₂ → ℓ₂ ≼ ℓ₁
  → ℓ₁ ≡ ℓ₂
≼-antisym l⊑l l⊑l = refl
≼-antisym h⊑h h⊑h = refl

≾-antisym : ∀ {g₁ g₂}
  → g₁ ≾ g₂ → g₂ ≾ g₁
  → g₁ ~ₗ g₂
≾-antisym ≾-⋆r _ = ~⋆
≾-antisym ≾-⋆l _ = ⋆~
≾-antisym (≾-l ℓ₁≼ℓ₂) (≾-l ℓ₂≼ℓ₂)
  rewrite ≼-antisym ℓ₁≼ℓ₂ ℓ₂≼ℓ₂ = ~ₗ-refl

≲ᵣ-antisym : ∀ {S T}
  → S ≲ᵣ T → T ≲ᵣ S
  → S ~ᵣ T
≲-antisym : ∀ {A B}
  → A ≲ B → B ≲ A
  → A ~ B

≲ᵣ-antisym ≲-ι ≲-ι = ~-ι
≲ᵣ-antisym (≲-ref A≲B B≲A) (≲-ref _ _) =
  ~-ref (≲-antisym A≲B B≲A)
≲ᵣ-antisym (≲-fun gc₂≾gc₁ C≲A B≲D) (≲-fun gc₁≾gc₂ A≲C D≲B) =
  ~-fun (≾-antisym gc₁≾gc₂ gc₂≾gc₁) (≲-antisym A≲C C≲A) (≲-antisym B≲D D≲B)

≲-antisym (≲-ty g₁≾g₂ S≲T) (≲-ty g₂≾g₁ T≲S) =
  ~-ty (≾-antisym g₁≾g₂ g₂≾g₁) (≲ᵣ-antisym S≲T T≲S)

~ₗ-sym : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → g₂ ~ₗ g₁
~ₗ-sym ⋆~ = ~⋆
~ₗ-sym ~⋆ = ⋆~
~ₗ-sym l~l = l~l
~ₗ-sym h~h = h~h

~ᵣ-sym : ∀ {S T} → S ~ᵣ T → T ~ᵣ S
~-sym  : ∀ {A B} → A ~ B → B ~ A

~ᵣ-sym ~-ι = ~-ι
~ᵣ-sym (~-ref A~B) = ~-ref (~-sym A~B)
~ᵣ-sym (~-fun gc₁~gc₂ A~C B~D) = ~-fun (~ₗ-sym gc₁~gc₂) (~-sym A~C) (~-sym B~D)

~-sym (~-ty g₁~g₂ S~T) = ~-ty (~ₗ-sym g₁~g₂) (~ᵣ-sym S~T)

{- Properties of consistent subtyping (≲):
        B
   ≲  / | <:
     /  |
    A - C
      ~
        B
   ≲  / | ~
     /  |
    A - C
      <:
-}
≾-prop : ∀ {g₁ g₂ : Label}
  → g₁ ≾ g₂
  → ∃[ g ] (g₁ ~ₗ g) × (g <:ₗ g₂)
≾-prop {g} {⋆} ≾-⋆r = ⟨ ⋆ , ⟨ ~⋆ , <:-⋆ ⟩ ⟩
≾-prop {⋆} {g} ≾-⋆l = ⟨ g , ⟨ ⋆~ , <:ₗ-refl ⟩ ⟩
≾-prop {l ℓ₁} {l ℓ₂} (≾-l ℓ₁≼ℓ₂) =
  ⟨ l ℓ₁ , ⟨ ~ₗ-refl , <:-l ℓ₁≼ℓ₂ ⟩ ⟩

≾-prop′ : ∀ {g₁ g₂ : Label}
  → g₁ ≾ g₂
  → ∃[ g ] (g₁ <:ₗ g) × (g ~ₗ g₂)
≾-prop′ {g} {⋆} ≾-⋆r = ⟨ g , ⟨ <:ₗ-refl , ~⋆ ⟩ ⟩
≾-prop′ {⋆} {g} ≾-⋆l = ⟨ ⋆ , ⟨ <:-⋆ , ⋆~ ⟩ ⟩
≾-prop′ {l ℓ₁} {l ℓ₂} (≾-l ℓ₁≼ℓ₂) =
  ⟨ l ℓ₂ , ⟨ <:-l ℓ₁≼ℓ₂ , ~ₗ-refl ⟩ ⟩

≲ᵣ-prop : ∀ {S T : RawType}
  → S ≲ᵣ T
  → ∃[ U ] (S ~ᵣ U) × (U <:ᵣ T)
≲-prop : ∀ {A B : Type}
  → A ≲ B
  → ∃[ C ] (A ~ C) × (C <: B)

≲ᵣ-prop′ : ∀ {S T : RawType}
  → S ≲ᵣ T
  → ∃[ U ] (S <:ᵣ U) × (U ~ᵣ T)
≲-prop′ : ∀ {A B : Type}
  → A ≲ B
  → ∃[ C ] (A <: C) × (C ~ B)

≲ᵣ-prop′ {` ι} {` ι} ≲-ι = ⟨ ` ι , ⟨ <:-ι , ~-ι ⟩ ⟩
≲ᵣ-prop′ {Ref A} {Ref B} (≲-ref A≲B B≲A) =
  ⟨ Ref A , ⟨ <:ᵣ-refl , ~-ref (≲-antisym A≲B B≲A) ⟩ ⟩
≲ᵣ-prop′ {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} (≲-fun gc₂≾gc₁ C≲A B≲D) =
  case ≾-prop gc₂≾gc₁ of λ where
    ⟨ gc , ⟨ gc₂~gc , gc<:gc₁ ⟩ ⟩ →
      case ⟨ ≲-prop C≲A , ≲-prop′ B≲D ⟩ of λ where
        ⟨ ⟨ A′ , ⟨ C~A′ , A′<:A ⟩ ⟩ , ⟨ B′ , ⟨ B<:B′ , B′~D ⟩ ⟩ ⟩ →
          ⟨ [ gc ] A′ ⇒ B′ , ⟨ <:-fun gc<:gc₁ A′<:A B<:B′ , ~-fun (~ₗ-sym gc₂~gc) (~-sym C~A′) B′~D ⟩ ⟩

≲-prop′ {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) =
  case ≾-prop′ g₁≾g₂ of λ where
    ⟨ g , ⟨ g₁<:g , g~g₂ ⟩ ⟩ →
      case ≲ᵣ-prop′ S≲T of λ where
        ⟨ U , ⟨ S<:U , U~T ⟩ ⟩ →
          ⟨ U of g , ⟨ <:-ty g₁<:g S<:U , ~-ty g~g₂ U~T ⟩ ⟩

≲ᵣ-prop {` ι} {` ι} ≲-ι = ⟨ ` ι , ⟨ ~-ι , <:-ι ⟩ ⟩
≲ᵣ-prop {Ref A} {Ref B} (≲-ref A≲B B≲A) =
  ⟨ Ref B , ⟨ ~-ref (≲-antisym A≲B B≲A) , <:ᵣ-refl ⟩ ⟩
≲ᵣ-prop {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} (≲-fun gc₂≾gc₁ C≲A B≲D) =
  case ≾-prop′ gc₂≾gc₁ of λ where
    ⟨ gc , ⟨ gc₂<:gc , gc~gc₁ ⟩ ⟩ →
      case ⟨ ≲-prop′ C≲A , ≲-prop B≲D ⟩ of λ where
        ⟨ ⟨ A′ , ⟨ C<:A′ , A′~A ⟩ ⟩ , ⟨ B′ , ⟨ B~B′ , B′<:D ⟩ ⟩ ⟩ →
          ⟨ [ gc ] A′ ⇒ B′ ,
            ⟨ ~-fun (~ₗ-sym gc~gc₁) (~-sym A′~A) B~B′ , <:-fun gc₂<:gc C<:A′ B′<:D ⟩ ⟩

≲-prop {S of g₁} {T of g₂} (≲-ty g₁≾g₂ S≲T) =
  case ≾-prop g₁≾g₂ of λ where
    ⟨ g , ⟨ g₁~g , g<:g₂ ⟩ ⟩ →
      case ≲ᵣ-prop S≲T of λ where
        ⟨ U , ⟨ S~U , U<:T ⟩ ⟩ →
          ⟨ U of g , ⟨ ~-ty g₁~g S~U , <:-ty g<:g₂ U<:T ⟩ ⟩

join-≼ : ∀ {ℓ₁ ℓ₂ ℓ}
  → ℓ₁ ⋎ ℓ₂ ≡ ℓ
  → ℓ₁ ≼ ℓ × ℓ₂ ≼ ℓ
join-≼ {high} {high} {high} refl = ⟨ h⊑h , h⊑h ⟩
join-≼ {high} {low} {high} refl = ⟨ h⊑h , l⊑h ⟩
join-≼ {low} {high} {high} refl = ⟨ l⊑h , h⊑h ⟩
join-≼ {low} {low} {low} refl = ⟨ l⊑l , l⊑l ⟩

meet-≼ : ∀ {ℓ₁ ℓ₂ ℓ}
  → ℓ₁ ⋏ ℓ₂ ≡ ℓ
  → ℓ ≼ ℓ₁ × ℓ ≼ ℓ₂
meet-≼ {high} {high} {high} refl = ⟨ h⊑h , h⊑h ⟩
meet-≼ {high} {low} {low} refl = ⟨ l⊑h , l⊑l ⟩
meet-≼ {low} {high} {low} refl = ⟨ l⊑l , l⊑h ⟩
meet-≼ {low} {low} {low} refl = ⟨ l⊑l , l⊑l ⟩

{- Consistency implies consistent subtyping (both directions) -}
~ₗ→≾ : ∀ {g₁ g₂} → g₁ ~ₗ g₂ → g₁ ≾ g₂ × g₂ ≾ g₁
~ₗ→≾ ⋆~ = ⟨ ≾-⋆l , ≾-⋆r ⟩
~ₗ→≾ ~⋆ = ⟨ ≾-⋆r , ≾-⋆l ⟩
~ₗ→≾ l~l = ⟨ ≾-l l⊑l , ≾-l l⊑l ⟩
~ₗ→≾ h~h = ⟨ ≾-l h⊑h , ≾-l h⊑h ⟩

~ᵣ→≲ᵣ : ∀ {S T} → S ~ᵣ T → S ≲ᵣ T × T ≲ᵣ S
~→≲ : ∀ {A B} → A ~ B → A ≲ B × B ≲ A

~ᵣ→≲ᵣ ~-ι = ⟨ ≲-ι , ≲-ι ⟩
~ᵣ→≲ᵣ (~-ref A~B) =
  case ~→≲ A~B of λ where
    ⟨ A≲B , B≲A ⟩ → ⟨ ≲-ref A≲B B≲A , ≲-ref B≲A A≲B ⟩
~ᵣ→≲ᵣ (~-fun gc₁~gc₂ A~C B~D) =
  case ~ₗ→≾ gc₁~gc₂ of λ where
    ⟨ gc₁≾gc₂ , gc₂≾gc₁ ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~D ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲D , D≲B ⟩ ⟩ →
          ⟨ ≲-fun gc₂≾gc₁ C≲A B≲D , ≲-fun gc₁≾gc₂ A≲C D≲B ⟩
~→≲ (~-ty g₁~g₂ S~T) =
  case ⟨ ~ₗ→≾ g₁~g₂ , ~ᵣ→≲ᵣ S~T ⟩ of λ where
    ⟨ ⟨ g₁≾g₂ , g₂≾g₁ ⟩ , ⟨ S≲T , T≲S ⟩ ⟩ →
      ⟨ ≲-ty g₁≾g₂ S≲T , ≲-ty g₂≾g₁ T≲S ⟩

grad-meet-~ₗ : ∀ {g₁ g₂ g}
  → g₁ ⊓ₗ g₂ ≡ just g
  → g₁ ~ₗ g × g₂ ~ₗ g
grad-meet-~ₗ {⋆} {⋆} {⋆} refl = ⟨ ⋆~ , ⋆~ ⟩
grad-meet-~ₗ {⋆} {l low} {l low} refl = ⟨ ⋆~ , l~l ⟩
grad-meet-~ₗ {⋆} {l high} {l high} refl = ⟨ ⋆~ , h~h ⟩
grad-meet-~ₗ {l high} {⋆} {l high} refl = ⟨ h~h , ⋆~ ⟩
grad-meet-~ₗ {l high} {l high} {l high} refl = ⟨ h~h , h~h ⟩
grad-meet-~ₗ {l low} {⋆} {l low} refl = ⟨ l~l , ⋆~ ⟩
grad-meet-~ₗ {l low} {l low} {l low} refl = ⟨ l~l , l~l ⟩

grad-meet-~ᵣ : ∀ {S T U}
  → S ⊓ᵣ T ≡ just U
  → S ~ᵣ U × T ~ᵣ U
grad-meet-~ : ∀ {A B C}
  → A ⊓ B ≡ just C
  → A ~ C × B ~ C

grad-meet-~ᵣ {` Bool} {` Bool} {` Bool} refl = ⟨ ~-ι , ~-ι ⟩
grad-meet-~ᵣ {` Unit} {` Unit} {` Unit} refl = ⟨ ~-ι , ~-ι ⟩
grad-meet-~ᵣ {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      λ { refl → ⟨ ~-ref A~C , ~-ref B~C ⟩ }
grad-meet-~ᵣ {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} {U}
  with gc₁ ⊓ₗ gc₂ in gc₁⊓gc₂≡gc | A ⊓ C in A⊓C≡A′ | B ⊓ D in B⊓D≡B′
... | just gc | just A′ | just B′ =
  case grad-meet-~ₗ gc₁⊓gc₂≡gc of λ where
    ⟨ gc₁~gc , gc₂~gc ⟩ →
      case ⟨ grad-meet-~ {A} {C} A⊓C≡A′ , grad-meet-~ {B} {D} B⊓D≡B′ ⟩ of λ where
        ⟨ ⟨ A~A′ , C~A′ ⟩ , ⟨ B~B′ , D~B′ ⟩ ⟩ →
          λ { refl → ⟨ ~-fun gc₁~gc A~A′ B~B′ , ~-fun gc₂~gc C~A′ D~B′ ⟩ }
grad-meet-~ {S of g₁} {T of g₂} {C}
  with S ⊓ᵣ T in S⊓T≡U | g₁ ⊓ₗ g₂ in g₁⊓g₂≡g
... | just U | just g =
  case ⟨ grad-meet-~ᵣ {S} {T} S⊓T≡U , grad-meet-~ₗ g₁⊓g₂≡g ⟩ of λ where
    ⟨ ⟨ S~U , T~U ⟩ , ⟨ g₁~g , g₂~g ⟩ ⟩ →
      λ { refl → ⟨ ~-ty g₁~g S~U , ~-ty g₂~g T~U ⟩ }

{- Operator ∨̃ goes up in the ≲ lattice while ∧̃ goes down -}
consis-meet-≾ : ∀ {g₁ g₂ g}
  → g₁ ⋏̃ g₂ ≡ g
  → g ≾ g₁ × g ≾ g₂
consis-meet-≾ {⋆} {⋆} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-meet-≾ {⋆} {l low} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆l ⟩
consis-meet-≾ {⋆} {l high} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆l ⟩
consis-meet-≾ {l low} {⋆} {⋆} refl = ⟨ ≾-⋆l , ≾-⋆r ⟩
consis-meet-≾ {l high} {⋆} {⋆} refl = ⟨ ≾-⋆l , ≾-⋆r ⟩
consis-meet-≾ {l ℓ₁} {l ℓ₂} {l ℓ} refl =
  case meet-≼ {ℓ₁} {ℓ₂} {ℓ} refl of λ where
    ⟨ ℓ₁⋏ℓ₂≼ℓ₁ , ℓ₁⋏ℓ₂≼ℓ₂ ⟩ → ⟨ ≾-l ℓ₁⋏ℓ₂≼ℓ₁ , ≾-l ℓ₁⋏ℓ₂≼ℓ₂ ⟩

consis-join-≾ : ∀ {g₁ g₂ g}
  → g₁ ⋎̃ g₂ ≡ g
  → g₁ ≾ g × g₂ ≾ g
consis-join-≾ {⋆} {⋆} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-join-≾ {⋆} {l low} {⋆} refl = ⟨ ≾-⋆l , ≾-⋆r ⟩
consis-join-≾ {⋆} {l high} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-join-≾ {l high} {⋆} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-join-≾ {l low} {⋆} {⋆} refl = ⟨ ≾-⋆r , ≾-⋆r ⟩
consis-join-≾ {l ℓ₁} {l ℓ₂} {l ℓ} refl =
  case join-≼ {ℓ₁} {ℓ₂} {ℓ} refl of λ where
    ⟨ ℓ₁≼ℓ₁⋎ℓ₂ , ℓ₂≼ℓ₁⋎ℓ₂ ⟩ → ⟨ ≾-l ℓ₁≼ℓ₁⋎ℓ₂ , ≾-l ℓ₂≼ℓ₁⋎ℓ₂ ⟩


consis-meet-≲ᵣ : ∀ {S T U}
  → S ∧̃ᵣ T ≡ just U
  → U ≲ᵣ S × U ≲ᵣ T
consis-meet-≲ : ∀ {A B C}
  → A ∧̃ B ≡ just C
  → C ≲ A × C ≲ B
consis-join-≲ᵣ : ∀ {S T U}
  → S ∨̃ᵣ T ≡ just U
  → S ≲ᵣ U × T ≲ᵣ U
consis-join-≲ : ∀ {A B C}
  → A ∨̃ B ≡ just C
  → A ≲ C × B ≲ C

consis-meet-≲ᵣ {` Bool} {` Bool} {` Bool} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-meet-≲ᵣ {` Unit} {` Unit} {` Unit} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-meet-≲ᵣ {` Bool} {Ref _} {_} ()
consis-meet-≲ᵣ {` Unit} {Ref _} {_} ()
consis-meet-≲ᵣ {` Bool} {[ _ ] _ ⇒ _} {_} ()
consis-meet-≲ᵣ {` Unit} {[ _ ] _ ⇒ _} {_} ()
consis-meet-≲ᵣ {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~C ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲C , C≲B ⟩ ⟩ →
          λ { refl → ⟨ ≲-ref C≲A A≲C , ≲-ref C≲B B≲C ⟩ }
consis-meet-≲ᵣ {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} {U}
  with A ∨̃ C in A∨̃C≡A′ | B ∧̃ D in B∧̃D≡B′
... | just A′ | just B′ =
  case consis-join-≾ {gc₁} {gc₂} refl of λ where
    ⟨ gc₁≾gc₁⋎̃gc₂ , gc₂≾gc₁⋎̃gc₂ ⟩ →
      case ⟨ consis-join-≲ {A} {C} A∨̃C≡A′ , consis-meet-≲ {B} {D} B∧̃D≡B′ ⟩ of λ where
        ⟨ ⟨ A≲A′ , C≲A′ ⟩ , ⟨ B′≲B , B′≲D ⟩ ⟩ →
          λ { refl → ⟨ ≲-fun gc₁≾gc₁⋎̃gc₂ A≲A′ B′≲B , ≲-fun gc₂≾gc₁⋎̃gc₂ C≲A′ B′≲D ⟩ }
consis-meet-≲ {S of g₁} {T of g₂} {C}
  with S ∧̃ᵣ T in S∧̃T≡U
... | just U =
  case ⟨ consis-meet-≲ᵣ {S} {T} S∧̃T≡U , consis-meet-≾ {g₁} {g₂} refl ⟩ of λ where
    ⟨ ⟨ U≲S , U≲T ⟩ , ⟨ g₁⋏̃g₂≾g₁ , g₁⋏̃g₂≾g₂ ⟩ ⟩ →
      λ { refl → ⟨ ≲-ty g₁⋏̃g₂≾g₁ U≲S , ≲-ty g₁⋏̃g₂≾g₂ U≲T ⟩ }

consis-join-≲ᵣ {` Bool} {` Bool} {` Bool} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-join-≲ᵣ {` Unit} {` Unit} {` Unit} refl = ⟨ ≲-ι , ≲-ι ⟩
consis-join-≲ᵣ {` Bool} {Ref _} {_} ()
consis-join-≲ᵣ {` Unit} {Ref _} {_} ()
consis-join-≲ᵣ {` Bool} {[ _ ] _ ⇒ _} {_} ()
consis-join-≲ᵣ {` Unit} {[ _ ] _ ⇒ _} {_} ()
consis-join-≲ᵣ {Ref A} {Ref B} {U}
  with A ⊓ B in A⊓B≡C
... | just C =
  case grad-meet-~ {A} {B} A⊓B≡C of λ where
    ⟨ A~C , B~C ⟩ →
      case ⟨ ~→≲ A~C , ~→≲ B~C ⟩ of λ where
        ⟨ ⟨ A≲C , C≲A ⟩ , ⟨ B≲C , C≲B ⟩ ⟩ →
          λ { refl → ⟨ ≲-ref A≲C C≲A , ≲-ref B≲C C≲B ⟩ }
consis-join-≲ᵣ {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} {U}
  with A ∧̃ C in A∧̃C≡A′ | B ∨̃ D in B∨̃D≡B′
... | just A′ | just B′ =
  case consis-meet-≾ {gc₁} {gc₂} refl of λ where
    ⟨ gc₁⋏̃gc₂≾gc₁ , gc₁⋏̃gc₂≾gc₂ ⟩ →
      case ⟨ consis-meet-≲ {A} {C} A∧̃C≡A′ , consis-join-≲ {B} {D} B∨̃D≡B′ ⟩ of λ where
        ⟨ ⟨ A′≲A , A′≲C ⟩ , ⟨ B≲B′ , D≲B′ ⟩ ⟩ →
          λ { refl → ⟨ ≲-fun gc₁⋏̃gc₂≾gc₁ A′≲A B≲B′ , ≲-fun gc₁⋏̃gc₂≾gc₂ A′≲C D≲B′ ⟩ }
consis-join-≲ {S of g₁} {T of g₂} {C}
  with S ∨̃ᵣ T in S∨̃T≡U
... | just U =
  case ⟨ consis-join-≲ᵣ {S} {T} S∨̃T≡U , consis-join-≾ {g₁} {g₂} refl ⟩ of λ where
    ⟨ ⟨ S≲U , T≲U ⟩ , ⟨ g₁≾g₁⋎̃g₂ , g₂≾g₁⋎̃g₂ ⟩ ⟩ →
      λ { refl → ⟨ ≲-ty g₁≾g₁⋎̃g₂ S≲U , ≲-ty g₂≾g₁⋎̃g₂ T≲U ⟩ }

join-≼′ : ∀ {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′}
  → ℓ₁ ≼ ℓ₁′
  → ℓ₂ ≼ ℓ₂′
  → (ℓ₁ ⋎ ℓ₂) ≼ (ℓ₁′ ⋎ ℓ₂′)
join-≼′ l⊑l l⊑l = l⊑l
join-≼′ l⊑l l⊑h = l⊑h
join-≼′ l⊑l h⊑h = h⊑h
join-≼′ l⊑h l⊑l = l⊑h
join-≼′ l⊑h l⊑h = l⊑h
join-≼′ l⊑h h⊑h = h⊑h
join-≼′ h⊑h _ = h⊑h

consis-join-<:ₗ : ∀ {g₁ g₁′ g₂ g₂′}
  → g₁ <:ₗ g₁′
  → g₂ <:ₗ g₂′
  → g₁ ⋎̃ g₂ <:ₗ g₁′ ⋎̃ g₂′
consis-join-<:ₗ <:-⋆ <:-⋆ = <:-⋆
consis-join-<:ₗ <:-⋆ (<:-l x) = <:-⋆
consis-join-<:ₗ (<:-l x) <:-⋆ = <:-⋆
consis-join-<:ₗ (<:-l ℓ₁≼ℓ₁′) (<:-l ℓ₂≼ℓ₂′) = <:-l (join-≼′ ℓ₁≼ℓ₁′ ℓ₂≼ℓ₂′)

<:ₗ-antisym : ∀ {g₁ g₂}
  → g₁ <:ₗ g₂ → g₂ <:ₗ g₁
  → g₁ ≡ g₂
<:ₗ-antisym <:-⋆ <:-⋆ = refl
<:ₗ-antisym (<:-l ℓ₁≼ℓ₂) (<:-l ℓ₂≼ℓ₁) = cong l (≼-antisym ℓ₁≼ℓ₂ ℓ₂≼ℓ₁)

<:ᵣ-antisym : ∀ {S T}
  → S <:ᵣ T → T <:ᵣ S
  → S ≡ T
<:-antisym : ∀ {A B}
  → A <: B → B <: A
  → A ≡ B
<:ᵣ-antisym <:-ι <:-ι = refl
<:ᵣ-antisym (<:-ref A<:B B<:A) (<:-ref _ _) = cong Ref_ (<:-antisym A<:B B<:A)
<:ᵣ-antisym {[ gc₁ ] A ⇒ B} {[ gc₂ ] C ⇒ D} (<:-fun gc₂<:gc₁ C<:A B<:D) (<:-fun gc₁<:gc₂ A<:C D<:B) =
  let eq1 : [ gc₁ ] A ⇒ B ≡ [ gc₁ ] C ⇒ D
      eq1 = cong₂ (λ □₁ □₂ → [ gc₁ ] □₁ ⇒ □₂) (<:-antisym A<:C C<:A) (<:-antisym B<:D D<:B)
      eq2 : [ gc₁ ] C ⇒ D ≡ [ gc₂ ] C ⇒ D
      eq2 = cong (λ □ → [ □ ] C ⇒ D) (<:ₗ-antisym gc₁<:gc₂ gc₂<:gc₁) in
    trans eq1 eq2
<:-antisym {S of g₁} {T of g₂} (<:-ty g₁<:g₂ S<:T) (<:-ty g₂<:g₁ T<:S) =
  cong₂ (λ □₁ □₂ → □₁ of □₂) (<:ᵣ-antisym S<:T T<:S) (<:ₗ-antisym g₁<:g₂ g₂<:g₁)

≼-trans : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → ℓ₁ ≼ ℓ₂ → ℓ₂ ≼ ℓ₃ → ℓ₁ ≼ ℓ₃
≼-trans l⊑l l⊑l = l⊑l
≼-trans l⊑l l⊑h = l⊑h
≼-trans l⊑h h⊑h = l⊑h
≼-trans h⊑h h⊑h = h⊑h

<:ₗ-trans : ∀ {g₁ g₂ g₃}
  → g₁ <:ₗ g₂ → g₂ <:ₗ g₃ → g₁ <:ₗ g₃
<:ₗ-trans <:-⋆ <:-⋆ = <:-⋆
<:ₗ-trans (<:-l ℓ₁≼ℓ₂) (<:-l ℓ₂≼ℓ₃) = <:-l (≼-trans ℓ₁≼ℓ₂ ℓ₂≼ℓ₃)

_≼?_ : ∀ ℓ₁ ℓ₂ → Dec (ℓ₁ ≼ ℓ₂)
high ≼? high = yes h⊑h
high ≼? low = no λ ()
low ≼? high = yes l⊑h
low ≼? low = yes l⊑l

Context = List Type
{- Addr ↦ Type -}
Heagcontext = List (Addr × Type)

