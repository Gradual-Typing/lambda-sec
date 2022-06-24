module Erasure where

open import Data.List using (List; _∷_; [])
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Utils

-- Replace every label by low
⌈_⌉ : Type → Type
⌈ ` ι of g ⌉           = ` ι of l low
⌈ Ref A of g ⌉         = Ref ⌈ A ⌉ of l low
⌈ [ gc ] A ⇒ B of g ⌉ = [ l low ] ⌈ A ⌉ ⇒ ⌈ B ⌉ of l low

-- Type erasure ⌈_⌉ preserves consistency
erasure-consis : ∀ {A B} → A ~ B → ⌈ A ⌉ ~ ⌈ B ⌉
erasure-consis (~-ty _ ~-ι) = ~-ty l~ ~-ι
erasure-consis (~-ty _ (~-ref A~B)) =
  ~-ty l~ (~-ref (erasure-consis A~B))
erasure-consis (~-ty _ (~-fun _ A~C B~D)) =
  ~-ty l~ (~-fun l~ (erasure-consis A~C) (erasure-consis B~D))

erase/c : ∀ {A B} → Cast A ⇒ B → Cast ⌈ A ⌉ ⇒ ⌈ B ⌉
erase/c (cast A B p A~B) = cast ⌈ A ⌉ ⌈ B ⌉ p (erasure-consis A~B)

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
  low  → ƛ[ low ] ⌈ A ⌉ ˙ (erase N) of low
  high → ●
erase (L · M) = erase L · erase M
erase (if L A M N) = if (erase L) ⌈ A ⌉ (erase M) (erase N)
erase (`let M N) = `let (erase M) (erase N)
erase (ref[ ℓ ] M) = ref[ low ] erase M
erase (ref?[ ℓ ] M) = ref?[ low ] erase M
erase (ref✓[ ℓ ] M) = ref✓[ low ] erase M
erase (! M) = ! erase M
erase (L := M) = erase L := erase M
erase (L :=? M) = erase L :=? erase M
erase (L :=✓ M) = erase L :=✓ erase M
erase (M ⟨ c ⟩) = erase M ⟨ erase/c c ⟩
erase (prot[ ℓ ] M) =
  case ℓ of λ where
  low  → prot[ low ] erase M
  high → ●
erase (cast-pc g M) = erase M
erase (error e) = error e
erase ● = ●

erase-μ : Heap → Heap
erase-μ [] = []
erase-μ (⟨ a , V , low  ⟩ ∷ μ) = ⟨ a , V , low ⟩ ∷ erase-μ μ
erase-μ (⟨ a , V , high ⟩ ∷ μ) = erase-μ μ
