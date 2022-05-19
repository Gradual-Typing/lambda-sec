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

infix 4 _⊇_

_⊇_ : HeapContext → HeapContext → Set
Σ′ ⊇ Σ = ∀ a {T ℓ} → key _≟_ Σ a ≡ just ⟨ T , ℓ ⟩ → key _≟_ Σ′ a ≡ just ⟨ T , ℓ ⟩

infix 4 _⊢_

_⊢_ : HeapContext → Heap → Set
Σ ⊢ μ = ∀ a {T ℓ}
  → key _≟_ Σ a ≡ just ⟨ T , ℓ ⟩
  → (a < length μ) ×
     (∃[ V ] (key _≟_ μ a ≡ just ⟨ V , ℓ ⟩) × ([] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ))


{- Properties about Σ′ ⊇ Σ : -}
⊇-refl : ∀ {Σ} → Σ ⊇ Σ
⊇-refl {Σ} a eq = eq

⊇-fresh : ∀ {Σ μ a₁ T ℓ} → Σ ⊢ μ → a₁ ≡ length μ → ⟨ a₁ , T , ℓ ⟩ ∷ Σ ⊇ Σ
⊇-fresh {Σ} {μ} {a₁} ⊢μ fresh a eq with a ≟ a₁
... | yes refl =
  let a<len   = proj₁ (⊢μ a eq)
      len<len = subst (λ □ → □ < length μ) fresh a<len in
    contradiction len<len (n≮n _)
... | no  _ = eq

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
relax-Σ (⊢cast ⊢M) Σ′⊇Σ = ⊢cast (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢ref ⊢M) Σ′⊇Σ = ⊢ref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢deref ⊢M) Σ′⊇Σ = ⊢deref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢assign ⊢L ⊢M) Σ′⊇Σ = ⊢assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢nsu-ref ⊢M) Σ′⊇Σ = ⊢nsu-ref (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢nsu-assign ⊢L ⊢M) Σ′⊇Σ = ⊢nsu-assign (relax-Σ ⊢L Σ′⊇Σ) (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢prot ⊢M) Σ′⊇Σ = ⊢prot (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢inj-pc ⊢M) Σ′⊇Σ = ⊢inj-pc (relax-Σ ⊢M Σ′⊇Σ)
relax-Σ (⊢proj-pc ⊢M pc≼ℓ) Σ′⊇Σ = ⊢proj-pc (relax-Σ ⊢M Σ′⊇Σ) pc≼ℓ
relax-Σ ⊢err Σ′⊇Σ = ⊢err
relax-Σ (⊢sub ⊢M A<:B) Σ′⊇Σ = ⊢sub (relax-Σ ⊢M Σ′⊇Σ) A<:B
relax-Σ (⊢sub-pc ⊢M gc<:gc′) Σ′⊇Σ = ⊢sub-pc (relax-Σ ⊢M Σ′⊇Σ) gc<:gc′

{- Properties about Σ ⊢ μ : -}
⊢μ-nil : [] ⊢ []
⊢μ-nil = λ a ()

⊢μ-ext : ∀ {Σ V a T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Σ ⊢ μ
  → a ≡ length μ  {- a is fresh in μ -}
    --------------------------------------------
  → ⟨ a , T , ℓ ⟩ ∷ Σ ⊢ ⟨ a , V , ℓ ⟩ ∷ μ
⊢μ-ext {Σ} {V₁} {a₁} {T₁} {ℓ₁} {μ} ⊢V₁ ⊢μ fresh a eq with a ≟ a₁
... | yes refl =
  case ⟨ eq , fresh ⟩ of λ where
    ⟨ refl , refl ⟩ → ⟨ ≤-refl , V₁ , refl , relax-Σ ⊢V₁ (⊇-fresh {μ = μ} ⊢μ fresh) ⟩
... | no _ =
  let ⟨ a<len , V , eq′ , ⊢V ⟩ = ⊢μ a eq in
    ⟨ <-trans a<len (n<1+n _) , V , eq′ , relax-Σ ⊢V (⊇-fresh {μ = μ} ⊢μ fresh) ⟩
