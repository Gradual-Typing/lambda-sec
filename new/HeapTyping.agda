{- Well-typedness of the heap -}

open import Data.Nat
open import Data.Nat.Properties using (n≮n; <-trans; n<1+n; ≤-refl)
open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; subst; cong)
open import Function using (case_of_)

open import Types

module HeapTyping where

open import Utils
open import Heap
open import CC

infix 4 _⊢_

_⊢_ : HeapContext → Heap → Set
Σ ⊢ μ = ∀ a {T ℓ}
  → nth Σ a ≡ just ⟨ T , ℓ ⟩
  → ∃[ V ] Value V × (key _≟_ μ a ≡ just ⟨ V , ℓ ⟩) × ([] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ)


relax-Σ : ∀ {Γ Σ Σ′ gc pc M A}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ′ ⊇ Σ
    ---------------------
  → Γ ; Σ′ ; gc ; pc ⊢ M ⦂ A
relax-Σ ⊢const Σ′⊇Σ = ⊢const
relax-Σ (⊢addr eq) Σ′⊇Σ = ⊢addr (Σ′⊇Σ _ eq)
relax-Σ (⊢var Γ∋x) Σ′⊇Σ = ⊢var Γ∋x
relax-Σ (⊢lam ⊢M) Σ′⊇Σ = ⊢lam (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢app ⊢L ⊢M) Σ′⊇Σ = ⊢app (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢if ⊢L ⊢M ⊢N) Σ′⊇Σ = ⊢if (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢let ⊢M ⊢N) Σ′⊇Σ = ⊢let (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)
relax-Σ (⊢ref ⊢M pc′≼ℓ) Σ′⊇Σ = ⊢ref (relax-Σ ⊢M Σ′⊇Σ) pc′≼ℓ
relax-Σ (⊢ref? ⊢M) Σ′⊇Σ = ⊢ref? (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢ref✓ ⊢M pc≼ℓ) Σ′⊇Σ = ⊢ref✓ (relax-Σ ⊢M Σ′⊇Σ) pc≼ℓ
relax-Σ (⊢deref ⊢M) Σ′⊇Σ = ⊢deref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢assign ⊢L ⊢M pc′≼ℓ) Σ′⊇Σ = ⊢assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) pc′≼ℓ
relax-Σ (⊢assign? ⊢L ⊢M) Σ′⊇Σ = ⊢assign? (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢assign✓ ⊢L ⊢M pc≼ℓ) Σ′⊇Σ = ⊢assign✓ (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ) pc≼ℓ
relax-Σ (⊢prot ⊢M) Σ′⊇Σ = ⊢prot (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢cast ⊢M) Σ′⊇Σ = ⊢cast (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢cast-pc ⊢M pc~g) Σ′⊇Σ = ⊢cast-pc (relax-Σ ⊢M Σ′⊇Σ) pc~g
relax-Σ ⊢err Σ′⊇Σ = ⊢err
relax-Σ (⊢sub ⊢M A<:B) Σ′⊇Σ = ⊢sub (relax-Σ ⊢M Σ′⊇Σ) A<:B
relax-Σ (⊢sub-pc ⊢M gc<:gc′) Σ′⊇Σ = ⊢sub-pc (relax-Σ ⊢M Σ′⊇Σ) gc<:gc′

{- Properties about Σ ⊢ μ : -}
⊢μ-nil : [] ⊢ []
⊢μ-nil = λ a ()

⊢μ-new : ∀ {Σ V a T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Value V
  → Σ ⊢ μ
  → a ≡ length Σ  {- a is fresh -}
    -----------------------------------------------
  → Σ ∷ʳ ⟨ T , ℓ ⟩ ⊢ ⟨ a , V , ℓ ⟩ ∷ μ
⊢μ-new {Σ} {V₁} {a₁} {T₁} {ℓ₁} {μ} ⊢V₁ v₁ ⊢μ refl a {T} {ℓ} eq
  with a ≟ length Σ
... | yes refl =
  case trans (sym eq) (snoc-here ⟨ T₁ , ℓ₁ ⟩ Σ) of λ where
  refl → ⟨ V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-snoc Σ ⟨ T₁ , ℓ₁ ⟩) ⟩
... | no neq =
  let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ a (snoc-there ⟨ T , ℓ ⟩ Σ eq neq) in
    ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-snoc Σ ⟨ T₁ , ℓ₁ ⟩) ⟩

⊢μ-update : ∀ {Σ V a T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Value V
  → Σ ⊢ μ
  → nth Σ a ≡ just ⟨ T , ℓ ⟩  {- updating a -}
    -----------------------------------------------
  → Σ ⊢ ⟨ a , V , ℓ ⟩ ∷ μ
⊢μ-update {Σ} {V₁} {a₁} {T₁} {ℓ₁} {μ} ⊢V₁ v₁ ⊢μ eq₁ a eq with a ≟ a₁
... | yes refl =
  case trans (sym eq) eq₁ of λ where
    refl → ⟨ V₁ , v₁ , refl , ⊢V₁ ⟩
... | no  _ = ⊢μ a eq
