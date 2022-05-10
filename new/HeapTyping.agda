{- Well-typedness of the heap -}

open import Data.Nat
open import Data.Nat.Properties using (n≮n; <-trans; n<1+n)
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

_⊇_ : HeapContext → HeapContext → Set
Σ′ ⊇ Σ = ∀ a {A} → key _≟_ Σ a ≡ just A → key _≟_ Σ′ a ≡ just A

infix 4 _⊢_

_⊢_ : HeapContext → Heap → Set
Σ ⊢ μ = (length Σ ≡ length μ) ×
  ∀ a {A} → key _≟_ Σ a ≡ just A
          → (a < length Σ) × (∃[ T ] ∃[ ℓ ] (A ≡ T of l ℓ) ×
               (∃[ V ] (key _≟_ μ a ≡ just ⟨ V , ℓ ⟩) × ([] ; Σ ; l low ; low ⊢ V ⦂ A)))


{- Properties about Σ′ ⊇ Σ : -}
⊇-refl : ∀ {Σ} → Σ ⊇ Σ
⊇-refl {Σ} a eq = eq

⊇-fresh : ∀ {Σ μ a₁ A₁} → Σ ⊢ μ → a₁ ≡ length μ → (⟨ a₁ , A₁ ⟩ ∷ Σ) ⊇ Σ
⊇-fresh {Σ} {μ} {a₁} {A₁} ⟨ len≡ , pred ⟩ fresh a {A} eq with a ≟ a₁
... | yes refl =
  let ⟨ a<len , _ ⟩ = pred a {A} eq in
  let len<len = subst (λ □ → □ < length Σ) (trans fresh (sym len≡)) a<len in
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
⊢μ-nil = ⟨ refl , (λ a {A} ()) ⟩

⊢μ-ext : ∀ {Σ V a T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Σ ⊢ μ
  → a ≡ length μ  {- a is fresh in μ -}
    --------------------------------------------
  → ⟨ a , T of l ℓ ⟩ ∷ Σ ⊢ ⟨ a , V , ℓ ⟩ ∷ μ
⊢μ-ext {Σ} {V₁} {a₁} {T₁} {ℓ₁} {μ} ⊢V₁ ⊢μ fresh = ⟨ cong suc (proj₁ ⊢μ) , wt ⟩
  where
  wt : _  {- Have to add this. I think this is a bug of Agda. -}
  wt a {A} eq with a ≟ a₁
  ... | yes refl =
    case eq of λ where
      refl → ⟨ a<1+len , T₁ , ℓ₁ , refl , V₁ , refl , relax-Σ ⊢V₁ (⊇-fresh {μ = μ} ⊢μ fresh) ⟩
    where
    a<1+len : a < 1 + (length Σ)
    a<1+len = subst (λ □ → a < 1 + □) (trans fresh (sym (proj₁ ⊢μ))) (n<1+n a)
  ... | no _ =
    let ⟨ a<len , T , ℓ , A≡Tℓ , V , eq′ , ⊢V ⟩ = (proj₂ ⊢μ) a eq in
      ⟨ <-trans a<len (n<1+n _) , T , ℓ , A≡Tℓ , V , eq′ , relax-Σ ⊢V (⊇-fresh {μ = μ} ⊢μ fresh) ⟩
