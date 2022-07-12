module RelatedHeaps where

open import Data.Nat
open import Data.List using (List; _∷_; [])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; subst; cong; cong₂)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import Heap
open import CC
open import Reduction
open import Utils

open import Erasure


{- Related heaps -}
infix 4 _≈_

_≈_ : ∀ (μ μ′ : Heap) → Set
μ ≈ μ′ = ∀ a {V ℓ}
  → key _≟_ μ a ≡ just ⟨ V , ℓ ⟩
  → case ℓ of λ where
     low  → key _≟_ μ′ a ≡ just ⟨ erase V , low  ⟩
     high → key _≟_ μ′ a ≡ just ⟨ ●      , high ⟩

μ≈-high-update : ∀ {μ μ′ a V₁ V₂} → μ ≈ μ′ → key _≟_ μ a ≡ just ⟨ V₁ , high ⟩ → ⟨ a , V₂ , high ⟩ ∷ μ ≈ μ′
μ≈-high-update {μ} {μ′} {a₁} {V₁} {V₂} μ≈ eq a {V} {ℓ} with a ≟ a₁
... | yes refl = λ { refl → μ≈ a eq }
... | no  _    = λ eq → μ≈ a eq

μ≈-low : ∀ {μ μ′ a V} → μ ≈ μ′ → ⟨ a , V , low ⟩ ∷ μ ≈ ⟨ a , erase V , low ⟩ ∷ μ′
μ≈-low {μ} {μ′} {a₁} {V₁} μ≈ a {ℓ = low}  with a ≟ a₁
... | yes _ = λ { refl → refl }
... | no  _ = λ eq → μ≈ a eq
μ≈-low {μ} {μ′} {a₁} {V₁} μ≈ a {ℓ = high} with a ≟ a₁
... | yes _ = λ ()
... | no _  = λ eq → μ≈ a eq


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

erase-pres-≈ : ∀ {μ μ′} → μ ≈ μ′ → μ ≈ erase-μ μ′
erase-pres-≈ μ≈μ′ a {V} {low} eq = let eq₁ = μ≈μ′ a eq in {!!}
erase-pres-≈ μ≈μ′ a {V} {high} = {!!}
