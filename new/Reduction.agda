open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Utils
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

  if□ : Type → Term → Term → Frame

  □⟨_⟩ : ∀ {A B} → Cast A ⇒ B → Frame

  nsu-assign□ : Term → Frame

  inj-pc□ : Frame

  proj-pc_□ : StaticLabel → Frame


plug : Term → Frame → Term
plug L (□· M)          = L · M
plug M ((V ·□) v)      = V · M
plug M ref[ ℓ ]□       = ref[ ℓ ] M
plug M !□              = ! M
plug L (□:= M)         = L := M
plug M ((V :=□) v)     = V := M
plug M (let□ N)        = `let M N
plug L (if□ A M N)     = if L A M N
plug M □⟨ c ⟩          = M ⟨ c ⟩
plug L (nsu-assign□ M) = nsu-assign L M
plug M inj-pc□         = inj-pc M
plug M (proj-pc ℓ □)   = proj-pc ℓ M


infix 2 _∣_∣_—→_∣_

data _∣_∣_—→_∣_ : Term → Heap → StaticLabel → Term → Heap → Set where

  ξ : ∀ {M M′ F μ μ′ pc}
    → M        ∣ μ ∣ pc —→ M′        ∣ μ′
      ---------------------------------------- ξ
    → plug M F ∣ μ ∣ pc —→ plug M′ F ∣ μ′

  ξ-err : ∀ {F μ pc e}
      ---------------------------------------------- ξ-error
    → plug (error e) F ∣ μ ∣ pc —→ error e ∣ μ

  prot-val : ∀ {V μ pc ℓ}
    → (v : Value V)
      --------------------------------------------------- ProtectVal
    → prot[ ℓ ] V ∣ μ ∣ pc —→ stamp-val V v ℓ ∣ μ

  prot-ctx : ∀ {M M′ μ μ′ pc ℓ}
    → M           ∣ μ ∣ pc ⋎ ℓ —→ M′           ∣ μ′
      --------------------------------------------------- ProtectContext
    → prot[ ℓ ] M ∣ μ ∣ pc     —→ prot[ ℓ ] M′ ∣ μ′

  prot-err : ∀ {μ pc ℓ e}
      --------------------------------------------------- ProtectContext
    → prot[ ℓ ] (error e) ∣ μ ∣ pc —→ error e ∣ μ

  β : ∀ {V N μ pc gc′ A ℓ}
    → Value V
      ------------------------------------------------------------------- β
    → (ƛ[ gc′ ] A ˙ N of ℓ) · V ∣ μ ∣ pc —→ prot[ ℓ ] (N [ V ]) ∣ μ

  β-if-true : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfTrue
    → if ($ true of ℓ) A M N ∣ μ ∣ pc —→ prot[ ℓ ] M ∣ μ

  β-if-false : ∀ {M N μ pc A ℓ}
      ----------------------------------------------------------------------- IfFalse
    → if ($ false of ℓ) A M N ∣ μ ∣ pc —→ prot[ ℓ ] N ∣ μ

  β-let : ∀ {V N μ pc}
    → Value V
      -------------------------------------- Let
    → `let V N ∣ μ ∣ pc —→ N [ V ] ∣ μ

  ref : ∀ {V μ pc a ℓ}
    → Value V
    → a ≡ length μ  {- address a is fresh -}
      ----------------------------------------------------------------- Ref
    → ref[ ℓ ] V ∣ μ ∣ pc —→ addr a of low ∣ ⟨ a , V , ℓ ⟩ ∷ μ

  nsu-ref-ok : ∀ {M μ pc ℓ}
    → pc ≼ ℓ
      -------------------------------------- NSURefSuccess
    → nsu-ref ℓ M ∣ μ ∣ pc —→ proj-pc ℓ M ∣ μ

  nsu-ref-fail : ∀ {M μ pc ℓ}
    → ¬ pc ≼ ℓ
      ------------------------------------------------- NSURefFail
    → nsu-ref ℓ M ∣ μ ∣ pc —→ error nsu-error ∣ μ

  deref : ∀ {V μ pc a ℓ ℓ₁}
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
      -------------------------------------------------- Deref
    → ! (addr a of ℓ) ∣ μ ∣ pc —→ prot[ ℓ ⋎ ℓ₁ ] V ∣ μ

  assign : ∀ {V V₁ μ pc a ℓ ℓ₁}
    → Value V
    → key _≟_ μ a ≡ just ⟨ V₁ , ℓ₁ ⟩
      --------------------------------------------------------------------- Assign
    → (addr a of ℓ) := V ∣ μ ∣ pc —→ $ tt of low ∣ ⟨ a , V , ℓ₁ ⟩ ∷ μ

  nsu-assign-ok : ∀ {V W M μ pc a ℓ ℓ₁}
    → (w : Value W) → unwrap W w ≡ addr a of ℓ {- W might be wrapped in casts -}
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
    → pc ≼ ℓ₁
      -------------------------------------- NSUAssignSuccess
    → nsu-assign W M ∣ μ ∣ pc —→ M ∣ μ

  nsu-assign-fail : ∀ {V W M μ pc a ℓ ℓ₁}
    → (w : Value W) → unwrap W w ≡ addr a of ℓ
    → key _≟_ μ a ≡ just ⟨ V , ℓ₁ ⟩
    → ¬ pc ≼ ℓ₁
      --------------------------------------------------- NSUAssignFail
    → nsu-assign W M ∣ μ ∣ pc —→ error nsu-error ∣ μ

  {- Reduction rules about casts, active and inert: -}
  cast : ∀ {Σ gc A B V μ pc pc′} {c : Cast A ⇒ B}
    → (⊢V : [] ; Σ ; gc ; pc′ ⊢ V ⦂ A)
    → (v : Value V)
    → (a : Active c)
      -------------------------------------------------- Cast
    → V ⟨ c ⟩ ∣ μ ∣ pc —→ apply-cast V ⊢V v c a ∣ μ

  if-cast-true : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      ----------------------------------------------------------------------- IfCastTrue
    → if ($ true of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot[ ℓ ] (inj-pc M) ⟨ stamp-c A ℓ c ⟩ ∣ μ

  if-cast-false : ∀ {M N μ pc A g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
      ----------------------------------------------------------------------- IfCastFalse
    → if ($ false of ℓ ⟨ c ⟩) A M N ∣ μ ∣ pc —→ prot[ ℓ ] (inj-pc N) ⟨ stamp-c A ℓ c ⟩ ∣ μ

  fun-cast : ∀ {V W μ pc A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → Value V → Value W
    → (i : Inert c)
      ---------------------------------------------------------------- FunCast
    → (V ⟨ c ⟩) · W ∣ μ ∣ pc —→ elim-fun-cast V W pc i ∣ μ

  deref-cast : ∀ {V μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V
    → Inert c
      ------------------------------------------------------ DerefCast
    → ! (V ⟨ c ⟩) ∣ μ ∣ pc —→ ! V ⟨ out-c c ⟩ ∣ μ

  assign-cast : ∀ {V W μ pc A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Value W
    → Inert c
      ------------------------------------------------------ AssignCast
    → (V ⟨ c ⟩) := W ∣ μ ∣ pc —→ V := (W ⟨ in-c c ⟩) ∣ μ

  β-inj-pc : ∀ {V μ pc}
    → Value V
      ------------------------------------- InjectedPC
    → inj-pc V ∣ μ ∣ pc —→ V ∣ μ

  β-proj-pc : ∀ {V μ pc ℓ}
    → Value V
      ------------------------------------- ProjectedPC
    → proj-pc ℓ V ∣ μ ∣ pc —→ V ∣ μ
