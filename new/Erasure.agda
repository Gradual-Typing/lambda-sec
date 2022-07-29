module Erasure where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong; cong₂)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import ErasedReduction
open import Utils


-- {- **** Type erasure **** -}
-- -- Replace every label by low
-- ⌈_⌉ : Type → Type
-- ⌈ ` ι of g ⌉           = ` ι of l low
-- ⌈ Ref A of g ⌉         = Ref ⌈ A ⌉ of l low
-- ⌈ [ gc ] A ⇒ B of g ⌉ = [ l low ] ⌈ A ⌉ ⇒ ⌈ B ⌉ of l low

-- -- Type erasure ⌈_⌉ preserves consistency
-- erasure-consis : ∀ {A B} → A ~ B → ⌈ A ⌉ ~ ⌈ B ⌉
-- erasure-consis (~-ty _ ~-ι) = ~-ty l~ ~-ι
-- erasure-consis (~-ty _ (~-ref A~B)) =
--   ~-ty l~ (~-ref (erasure-consis A~B))
-- erasure-consis (~-ty _ (~-fun _ A~C B~D)) =
--   ~-ty l~ (~-fun l~ (erasure-consis A~C) (erasure-consis B~D))

-- erase/c : ∀ {A B} → Cast A ⇒ B → Cast ⌈ A ⌉ ⇒ ⌈ B ⌉
-- erase/c (cast A B p A~B) = cast ⌈ A ⌉ ⌈ B ⌉ p (erasure-consis A~B)

{- **** Term erasure **** -}
erase : Term → Term
erase (addr a of ℓ) =
  case ℓ of λ where
  low  → addr a of low
  high → ●
erase ($ k of ℓ) =
  case ℓ of λ where
  low  → $ k of low
  high → ●
erase (` x) = ` x
erase (ƛ[ pc ] A ˙ N of ℓ) =
  case ℓ of λ where
  low  → ƛ[ pc ] A ˙ (erase N) of low
  high → ●
erase (L · M) = erase L · erase M
erase (if L A M N) = if (erase L) A (erase M) (erase N)
erase (`let M N) = `let (erase M) (erase N)
erase (ref[ ℓ ]  M) = ref[ ℓ ] erase M
erase (ref?[ ℓ ] M) = ref?[ ℓ ] erase M
erase (ref✓[ ℓ ] M) = ref✓[ ℓ ] erase M
erase (! M) = ! erase M
erase (L := M) = erase L := erase M
erase (L :=? M) = erase L :=? erase M
erase (L :=✓ M) = erase L :=✓ erase M
erase (M ⟨ c ⟩) = erase M  {- let's try simply deleting the cast -}
erase (prot ℓ M) =
  case ℓ of λ where
  low  → prot low (erase M)
  high → ●
erase (cast-pc g M) = erase M
erase (error e) = error e
erase ● = ●

erase-val-value : ∀ {V} (v : Value V) → Value (erase V)
erase-val-value (V-addr {ℓ = ℓ}) with ℓ
... | low  = V-addr
... | high = V-●
erase-val-value (V-ƛ {ℓ = ℓ}) with ℓ
... | low  = V-ƛ
... | high = V-●
erase-val-value (V-const {ℓ = ℓ}) with ℓ
... | low  = V-const
... | high = V-●
erase-val-value (V-cast v i) = erase-val-value v
erase-val-value V-● = V-●

erase-idem : ∀ M → erase M ≡ erase (erase M)
erase-idem (addr a of ℓ) with ℓ
... | low  = refl
... | high = refl
erase-idem ($ k of ℓ) with ℓ
... | low  = refl
... | high = refl
erase-idem (` x) = refl
erase-idem (ƛ[ pc ] A ˙ N of ℓ) with ℓ
... | low  = cong (ƛ[ pc ] A ˙_of low) (erase-idem N)
... | high = refl
erase-idem (L · M) = cong₂ _·_ (erase-idem L) (erase-idem M)
erase-idem (if L A M N) rewrite sym (erase-idem L) =
  cong₂ (if _ A) (erase-idem M) (erase-idem N)
erase-idem (`let M N) = cong₂ `let (erase-idem M) (erase-idem N)
erase-idem (ref[ ℓ ]  M) = cong ref[ ℓ ]_ (erase-idem M)
erase-idem (ref?[ ℓ ] M) = cong ref?[ ℓ ]_ (erase-idem M)
erase-idem (ref✓[ ℓ ] M) = cong ref✓[ ℓ ]_ (erase-idem M)
erase-idem (! M) = cong !_ (erase-idem M)
erase-idem (L := M) = cong₂ _:=_ (erase-idem L) (erase-idem M)
erase-idem (L :=? M) = cong₂ _:=?_ (erase-idem L) (erase-idem M)
erase-idem (L :=✓ M) = cong₂ _:=✓_ (erase-idem L) (erase-idem M)
erase-idem (M ⟨ c ⟩) = erase-idem M
erase-idem (prot ℓ M) with ℓ
... | low  = cong (prot low) (erase-idem M)
... | high = refl
erase-idem (cast-pc g M) = erase-idem M
erase-idem (error e) = refl
erase-idem ● = refl

erase-stamp-high : ∀ {V} (v : Value V) → erase (stamp-val V v high) ≡ ●
erase-stamp-high (V-addr {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-ƛ {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-const {ℓ = ℓ}) rewrite ℓ⋎high≡high {ℓ} = refl
erase-stamp-high (V-cast v i) = erase-stamp-high v
erase-stamp-high V-● = refl


erase-plug : ∀ {M₁ M₂ pc μ₁ μ₂} (F : Frame)
  → erase M₁ ∣ μ₁ ∣ pc —↠ₑ erase M₂ ∣ μ₂
  → erase (plug M₁ F) ∣ μ₁ ∣ pc —↠ₑ erase (plug M₂ F) ∣ μ₂
erase-plug (□· M) R* = plug-mult (□· erase M) R*
erase-plug ((V ·□) v) R* = plug-mult ((erase V ·□) (erase-val-value v)) R*
erase-plug (ref✓[ ℓ ]□) R* = plug-mult ref✓[ ℓ ]□ R*
erase-plug !□ R* = plug-mult !□ R*
erase-plug (□:=? M) R* = plug-mult (□:=? erase M) R*
erase-plug (□:=✓ M) R* = plug-mult (□:=✓ erase M) R*
erase-plug ((V :=✓□) v) R* = plug-mult ((erase V :=✓□) (erase-val-value v)) R*
erase-plug (let□ N) R* = plug-mult (let□ erase N) R*
erase-plug (if□ A M N) R* = plug-mult (if□ A (erase M) (erase N)) R*
erase-plug □⟨ c ⟩ R* = R*
erase-plug cast-pc g □ R* = R*

{- Predicate of erased term -}
data Erased : Term → Set where
  e-var   : ∀ {x} → Erased (` x)
  e-●      : Erased ●
  e-ƛ       : ∀ {pc A N}        → Erased N → Erased (ƛ[ pc ] A ˙ N of low)
  e-const   : ∀ {ι} {k : rep ι} → Erased ($ k of low)
  e-addr    : ∀ {a}             → Erased (addr a of low)
  e-app     : ∀ {L M}           → Erased L → Erased M → Erased (L · M)
  e-if      : ∀ {A L M N}       → Erased L → Erased M → Erased N → Erased (if L A M N)
  e-let     : ∀ {M N}           → Erased M → Erased N → Erased (`let M N)
  e-ref     : ∀ {M ℓ}           → Erased M → Erased (ref[ ℓ ] M)
  e-ref?    : ∀ {M ℓ}           → Erased M → Erased (ref?[ ℓ ] M)
  e-ref✓    : ∀ {M ℓ}           → Erased M → Erased (ref✓[ ℓ ] M)
  e-deref   : ∀ {M}             → Erased M → Erased (! M)
  e-assign  : ∀ {L M}           → Erased L → Erased M → Erased (L := M)
  e-assign? : ∀ {L M}           → Erased L → Erased M → Erased (L :=? M)
  e-assign✓ : ∀ {L M}           → Erased L → Erased M → Erased (L :=✓ M)
  e-prot    : ∀ {M}             → Erased M → Erased (prot low M)
  e-error   : ∀ {e}             → Erased (error e)

erase-is-erased : ∀ M → Erased (erase M)
erase-is-erased (addr a of low) = e-addr
erase-is-erased (addr a of high) = e-●
erase-is-erased ($ k of low) = e-const
erase-is-erased ($ k of high) = e-●
erase-is-erased (` x) = e-var
erase-is-erased (ƛ[ pc ] A ˙ N of low) = e-ƛ (erase-is-erased N)
erase-is-erased (ƛ[ pc ] A ˙ N of high) = e-●
erase-is-erased (L · M) = e-app (erase-is-erased L) (erase-is-erased M)
erase-is-erased (if L A M N) = e-if (erase-is-erased L) (erase-is-erased M) (erase-is-erased N)
erase-is-erased (`let M N) = e-let (erase-is-erased M) (erase-is-erased N)
erase-is-erased (ref[ ℓ ] M) = e-ref (erase-is-erased M)
erase-is-erased (ref?[ ℓ ] M) = e-ref? (erase-is-erased M)
erase-is-erased (ref✓[ ℓ ] M) = e-ref✓ (erase-is-erased M)
erase-is-erased (! M) = e-deref (erase-is-erased M)
erase-is-erased (L := M) = e-assign (erase-is-erased L) (erase-is-erased M)
erase-is-erased (L :=? M) = e-assign? (erase-is-erased L) (erase-is-erased M)
erase-is-erased (L :=✓ M) = e-assign✓ (erase-is-erased L) (erase-is-erased M)
erase-is-erased (M ⟨ c ⟩) = erase-is-erased M
erase-is-erased (prot low M) = e-prot (erase-is-erased M)
erase-is-erased (prot high M) = e-●
erase-is-erased (cast-pc g M) = erase-is-erased M
erase-is-erased (error e) = e-error
erase-is-erased ● = e-●


{- **** Heap erasure **** -}
erase-μ : Heap → Heap
erase-μ [] = []
erase-μ (⟨ a , V , low  ⟩ ∷ μ) = ⟨ a , erase V , low ⟩ ∷ erase-μ μ
erase-μ (⟨ a , V , high ⟩ ∷ μ) = ⟨ a , ● , high ⟩ ∷ erase-μ μ
