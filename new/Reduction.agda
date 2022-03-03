open import Heap

open import Types
open import TypeBasedCast
open import CC

module Reduction where

data Frame : Set where
  □·_ : Term → Frame

  _·□ : (V : Term) → Value V → Frame

  ref[_]□ : StaticLabel → Frame

  !□ : Frame

  □:=_ : Term → Frame

  _:=□ : (V : Term) → Value V → Frame

  let□ : Term → Frame

  if□ : Term → Term → Frame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → Frame

  nsu-assign□ : Term → Frame


plug : Term → Frame → Term
plug L (□· M)          = L · M
plug M ((V ·□) v)      = V · M
plug M ref[ ℓ ]□       = ref[ ℓ ] M
plug M !□              = ! M
plug L (□:= M)         = L := M
plug M ((V :=□) v)     = V := M
plug M (let□ N)        = `let M N
plug L (if□ M N)       = if L then M else N endif
plug M □⟨ c ⟩          = M ⟨ c ⟩
plug L (nsu-assign□ M) = nsu-assign L M


data _∣_∣_—→_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ pc}
    → M        ∣ μ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ plug M′ F ∣ μ′

  ξ-error : ∀ {}
