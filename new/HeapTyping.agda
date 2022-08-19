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
-- Σ ⊢ μ = ∀ a {T ℓ}
--   → nth Σ a ≡ just ⟨ T , ℓ ⟩
--   → ∃[ V ] Value V × (key _≟_ μ a ≡ just ⟨ V , ℓ ⟩) × ([] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ)
Σ ⊢ μ = ∀ n ℓ {T}
  → lookup-Σ Σ (a[ ℓ ] n) ≡ just T
  → ∃[ V ] Value V × (lookup-μ μ (a[ ℓ ] n) ≡ just V) × ([] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ)


relax-Σ : ∀ {Γ Σ Σ′ gc pc M A}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  → Σ′ ⊇ Σ
    ---------------------
  → Γ ; Σ′ ; gc ; pc ⊢ M ⦂ A
relax-Σ ⊢const Σ′⊇Σ = ⊢const
relax-Σ (⊢addr {n = n} {ℓ₁ = ℓ₁} eq) Σ′⊇Σ = ⊢addr (Σ′⊇Σ (a[ ℓ₁ ] n) eq)
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
⊢μ-nil : ∅ ⊢ ∅
⊢μ-nil n low  ()
⊢μ-nil n high ()

-- ⊢μ-new : ∀ {Σ V a T ℓ μ}
--   → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
--   → Value V
--   → Σ ⊢ μ
--   → a ≡ length Σ  {- a is fresh -}
--     -----------------------------------------------
--   → Σ ∷ʳ ⟨ T , ℓ ⟩ ⊢ ⟨ a , V , ℓ ⟩ ∷ μ
-- ⊢μ-new {Σ} {V₁} {a₁} {T₁} {ℓ₁} {μ} ⊢V₁ v₁ ⊢μ refl a {T} {ℓ} eq
--   with a ≟ length Σ
-- ... | yes refl =
--   case trans (sym eq) (snoc-here ⟨ T₁ , ℓ₁ ⟩ Σ) of λ where
--   refl → ⟨ V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-snoc Σ ⟨ T₁ , ℓ₁ ⟩) ⟩
-- ... | no neq =
--   let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ a (snoc-there ⟨ T , ℓ ⟩ Σ eq neq) in
--     ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-snoc Σ ⟨ T₁ , ℓ₁ ⟩) ⟩

⊢μ-new : ∀ {Σ V n T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Value V
  → Σ ⊢ μ
  → (a[ ℓ ] n) FreshIn Σ
    -----------------------------------------------
  → ext-Σ ℓ T Σ ⊢ cons-μ (a[ ℓ ] n) V μ
⊢μ-new {⟨ Σᴸ , Σᴴ ⟩} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ refl n low {T} eq
  with n ≟ length Σᴸ
... | yes refl =
  case trans (sym eq) (snoc-here T₁ Σᴸ) of λ where
  refl {- T₁ ≡ T -} → ⟨ V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-ext low T ⟨ Σᴸ , Σᴴ ⟩) ⟩
... | no neq =
  let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ n low (snoc-there T Σᴸ eq neq) in
  ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-ext low T₁ ⟨ Σᴸ , Σᴴ ⟩) ⟩
⊢μ-new {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ refl n high {T} eq =
  let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ n high eq in
  ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-ext low T₁ Σ) ⟩
⊢μ-new {⟨ Σᴸ , Σᴴ ⟩} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ refl n high {T} eq
  with n ≟ length Σᴴ
... | yes refl =
  case trans (sym eq) (snoc-here T₁ Σᴴ) of λ where
  refl {- T₁ ≡ T -} → ⟨ V₁ , v₁ , refl , relax-Σ ⊢V₁ (⊇-ext high T ⟨ Σᴸ , Σᴴ ⟩) ⟩
... | no neq =
  let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ n high (snoc-there T Σᴴ eq neq) in
  ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-ext high T₁ ⟨ Σᴸ , Σᴴ ⟩) ⟩
⊢μ-new {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ refl n low {T} eq =
  let ⟨ V , v , eq′ , ⊢V ⟩ = ⊢μ n low eq in
  ⟨ V , v , eq′ , relax-Σ ⊢V (⊇-ext high T₁ Σ) ⟩

⊢μ-update : ∀ {Σ V n T ℓ μ}
  → [] ; Σ ; l low ; low ⊢ V ⦂ T of l ℓ
  → Value V
  → Σ ⊢ μ
  → lookup-Σ Σ (a[ ℓ ] n) ≡ just T  {- updating a -}
    -----------------------------------------------
  → Σ ⊢ cons-μ (a[ ℓ ] n) V μ
⊢μ-update {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ eq₁ n low eq with n ≟ n₁
... | yes refl =
  case trans (sym eq) eq₁ of λ where
    refl → ⟨ V₁ , v₁ , refl , ⊢V₁ ⟩
... | no  _ = ⊢μ n low eq
⊢μ-update {Σ} {V₁} {n₁} {T₁} {low} {μ} ⊢V₁ v₁ ⊢μ eq₁ n high = ⊢μ n high
⊢μ-update {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ eq₁ n high eq with n ≟ n₁
... | yes refl =
  case trans (sym eq) eq₁ of λ where
    refl → ⟨ V₁ , v₁ , refl , ⊢V₁ ⟩
... | no  _ = ⊢μ n high eq
⊢μ-update {Σ} {V₁} {n₁} {T₁} {high} {μ} ⊢V₁ v₁ ⊢μ eq₁ n low = ⊢μ n low
