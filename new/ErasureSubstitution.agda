module ErasureSubstitution where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst; subst₂; cong; cong₂)
open import Function using (case_of_)

open import Syntax

open import Utils
open import Types
open import TypeBasedCast
open import CC
open import Erasure

erase-σ : Subst → Subst
erase-σ σ = λ x → erase (σ x)

-- ext-erase : ∀ σ x → (ext (erase-σ σ)) x ≡ (erase-σ (ext σ)) x
-- ext-erase σ zero = refl
-- ext-erase σ (suc x) = sym goal
--   where
--   goal : erase (rename (↑ 1) (σ x)) ≡ rename (↑ 1) ((erase-σ σ) x)
--   goal = {!!}

-- subst-erase : ∀ σ M → erase (⟪ σ ⟫ M) ≡ ⟪ erase-σ σ ⟫ (erase M)
-- subst-erase σ (` x) = refl
-- subst-erase σ (`let M N) =
--   cong₂ (λ □₁ □₂ → `let □₁ □₂) (subst-erase σ M) {!!}

postulate
  substitution-erase : ∀ N M → erase (N [ M ]) ≡ erase N [ erase M ]
