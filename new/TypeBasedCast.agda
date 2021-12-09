module TypeBasedCast where

open import Types
open import BlameLabels

data Cast_⇒_ : Type → Type → Set where
  cast : ∀ A B → BlameLabel → (A~B : A ~ B) → Cast A ⇒ B
