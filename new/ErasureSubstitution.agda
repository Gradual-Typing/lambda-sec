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
open import Addr
open import TypeBasedCast
open import CC
open import Erasure

erase-σ : Subst → Subst
erase-σ σ = λ x → erase (σ x)

rename-erase : ∀ ρ M → erase (rename ρ M) ≡ rename ρ (erase M)
rename-erase ρ (` x) = refl
{- values -}
rename-erase ρ (addr a[ low ] n of low) = refl
rename-erase ρ (addr a[ low ] n of high) = refl
rename-erase ρ (addr a[ high ] n of low) = refl
rename-erase ρ (addr a[ high ] n of high) = refl
rename-erase ρ (ƛ[ pc ] A ˙ N of low)
  rewrite rename-erase (ext ρ) N = refl
rename-erase ρ (ƛ[ pc ] A ˙ N of high) = refl
rename-erase ρ ($ k of low) = refl
rename-erase ρ ($ k of high) = refl
{- -- -}
rename-erase ρ (M · N)
  rewrite rename-erase ρ M | rename-erase ρ N = refl
rename-erase ρ (`let M N)
  rewrite rename-erase ρ M | rename-erase (ext ρ) N = refl
rename-erase ρ (if L A M N)
  rewrite rename-erase ρ L | rename-erase ρ M | rename-erase ρ N =
  refl
rename-erase ρ (ref[ ℓ ] M) rewrite rename-erase ρ M = refl
rename-erase ρ (ref?[ ℓ ] M) rewrite rename-erase ρ M = refl
rename-erase ρ (ref✓[ ℓ ] M) rewrite rename-erase ρ M = refl
rename-erase ρ (! M) rewrite rename-erase ρ M = refl
rename-erase ρ (L := M)
  rewrite rename-erase ρ L | rename-erase ρ M = refl
rename-erase ρ (L :=? M)
  rewrite rename-erase ρ L | rename-erase ρ M = refl
rename-erase ρ (L :=✓ M)
  rewrite rename-erase ρ L | rename-erase ρ M = refl
rename-erase ρ (M ⟨ c ⟩) rewrite rename-erase ρ M = refl
rename-erase ρ (cast-pc g M) rewrite rename-erase ρ M = refl
rename-erase ρ (prot low M) rewrite rename-erase ρ M = refl
rename-erase ρ (prot high M) = refl
rename-erase ρ (error e) = refl
rename-erase ρ ● = refl

ext-erase : ∀ σ → ext (erase-σ σ) ≡ erase-σ (ext σ)
ext-erase σ = extensionality (ext-erase-x σ)
  where
  ext-erase-x : ∀ σ x → (ext (erase-σ σ)) x ≡ (erase-σ (ext σ)) x
  ext-erase-x σ zero = refl
  ext-erase-x σ (suc x) = sym goal
    where
    goal : erase (rename (↑ 1) (σ x)) ≡ rename (↑ 1) ((erase-σ σ) x)
    goal rewrite rename-erase (↑ 1) (σ x) = refl

subst-erase : ∀ σ M → erase (⟪ σ ⟫ M) ≡ ⟪ erase-σ σ ⟫ (erase M)
subst-erase σ (` x) = refl
subst-erase σ (`let M N)
  rewrite subst-erase σ M | subst-erase (ext σ) N | ext-erase σ = refl

postulate
  substitution-erase : ∀ N M → erase (N [ M ]) ≡ erase N [ erase M ]
