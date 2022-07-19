module Frame where

open import Types
open import TypeBasedCast
open import CC

data Frame : Set where
  □·_ : Term → Frame

  _·□ : (V : Term) → Value V → Frame

  ref✓[_]□ : StaticLabel → Frame

  !□ : Frame

  □:=?_ : Term → Frame

  □:=✓_ : Term → Frame

  _:=✓□ : (V : Term) → Value V → Frame

  let□_ : Term → Frame

  if□ : Type → Term → Term → Frame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → Frame

  cast-pc_□ : Label → Frame


plug : Term → Frame → Term
plug L (□· M)          = L · M
plug M ((V ·□) v)      = V · M
plug M ref✓[ ℓ ]□      = ref✓[ ℓ ] M
plug M !□              = ! M
plug L (□:=? M)        = L :=? M
plug L (□:=✓ M)        = L :=✓ M
plug M ((V :=✓□) v)    = V :=✓ M
plug M (let□ N)        = `let M N
plug L (if□ A M N)     = if L A M N
plug M □⟨ c ⟩          = M ⟨ c ⟩
plug M (cast-pc g □)   = cast-pc g M

