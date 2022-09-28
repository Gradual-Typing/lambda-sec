module BigStepErasedDeterministic where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; trans; cong; sym)
open import Function using (case_of_)

open import Utils
open import Heap
open import Types
open import TypeBasedCast
open import CC

open import BigStepErased

determinism : ∀ {M μ μ₁ μ₂ pc} {V₁ V₂}
  → μ ∣ pc ⊢ M ⇓ₑ V₁ ∣ μ₁
  → μ ∣ pc ⊢ M ⇓ₑ V₂ ∣ μ₂
    -------------------------------------
  → V₁ ≡ V₂ × μ₁ ≡ μ₂
determinism (⇓ₑ-val _) (⇓ₑ-val _) = ⟨ refl , refl ⟩
determinism (⇓ₑ-app L⇓ƛN M⇓V N[V]⇓W) (⇓ₑ-app L⇓ƛN† M⇓V† N[V]⇓W†) =
  case determinism L⇓ƛN L⇓ƛN† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ →
      case determinism N[V]⇓W N[V]⇓W† of λ where
      ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-app L⇓ƛN _ _) (⇓ₑ-app-● L⇓● _) =
  contradiction (determinism L⇓ƛN L⇓●) (λ ())
determinism (⇓ₑ-app-● L⇓● _) (⇓ₑ-app L⇓ƛN _ _) =
  contradiction (determinism L⇓● L⇓ƛN) (λ ())
determinism (⇓ₑ-app-● L⇓● M⇓V) (⇓ₑ-app-● L⇓●† M⇓V†) =
  case determinism L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-if-true L⇓true M⇓V) (⇓ₑ-if-true L⇓true† M⇓V†) =
  case determinism L⇓true L⇓true† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-if-true L⇓true _) (⇓ₑ-if-false L⇓false _) =
  contradiction (determinism L⇓true L⇓false) (λ ())
determinism (⇓ₑ-if-true L⇓true _) (⇓ₑ-if-● L⇓●) =
  contradiction (determinism L⇓true L⇓●) (λ ())
determinism (⇓ₑ-if-false L⇓false N⇓V) (⇓ₑ-if-false L⇓false† N⇓V†) =
  case determinism L⇓false L⇓false† of λ where
  ⟨ refl , refl ⟩ →
    case determinism N⇓V N⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-if-false L⇓false _) (⇓ₑ-if-true L⇓true _) =
  contradiction (determinism L⇓false L⇓true) (λ ())
determinism (⇓ₑ-if-false L⇓false _) (⇓ₑ-if-● L⇓●) =
  contradiction (determinism L⇓false L⇓●) (λ ())
determinism (⇓ₑ-if-● L⇓●) (⇓ₑ-if-true L⇓true _) =
  contradiction (determinism L⇓● L⇓true ) (λ ())
determinism (⇓ₑ-if-● L⇓●) (⇓ₑ-if-false L⇓false _) =
  contradiction (determinism L⇓● L⇓false) (λ ())
determinism (⇓ₑ-if-● L⇓●) (⇓ₑ-if-● L⇓●†) =
  case determinism L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-let M⇓V N[V]⇓W) (⇓ₑ-let M⇓V† N[V]⇓W†) =
  case determinism M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case determinism N[V]⇓W N[V]⇓W† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-ref? M⇓V fresh _) (⇓ₑ-ref? M⇓V† fresh† _) =
  case determinism M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case trans fresh (sym fresh†) of λ where
      refl → ⟨ refl , refl ⟩
determinism (⇓ₑ-ref?-● M⇓V) (⇓ₑ-ref?-● M⇓V†) =
  case determinism M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-ref M⇓V fresh) (⇓ₑ-ref M⇓V† fresh†) =
  case determinism M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ →
    case trans fresh (sym fresh†) of λ where
      refl → ⟨ refl , refl ⟩
determinism (⇓ₑ-ref-● M⇓V) (⇓ₑ-ref-● M⇓V†) =
  case determinism M⇓V M⇓V† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-deref M⇓a eq) (⇓ₑ-deref M⇓a† eq†) =
  case determinism M⇓a M⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case trans (sym eq) eq† of λ where
    refl → ⟨ refl , refl ⟩
determinism (⇓ₑ-deref M⇓a _) (⇓ₑ-deref-● M⇓●) =
  contradiction (determinism M⇓a M⇓●) (λ ())
determinism (⇓ₑ-deref-● M⇓●) (⇓ₑ-deref M⇓a _) =
  contradiction (determinism M⇓● M⇓a) (λ ())
determinism (⇓ₑ-deref-● M⇓●) (⇓ₑ-deref-● M⇓●†) =
  case determinism M⇓● M⇓●† of λ where
  ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-assign? L⇓a M⇓V _) (⇓ₑ-assign? L⇓a† M⇓V† _) =
  case determinism L⇓a L⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-assign? L⇓a _ _) (⇓ₑ-assign?-● L⇓● _) =
  contradiction (determinism L⇓a L⇓●) (λ ())
determinism (⇓ₑ-assign?-● L⇓● _) (⇓ₑ-assign? L⇓a _ _) =
  contradiction (determinism L⇓● L⇓a) (λ ())
determinism (⇓ₑ-assign?-● L⇓● M⇓V) (⇓ₑ-assign?-● L⇓●† M⇓V†) =
  case determinism L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-assign L⇓a M⇓V) (⇓ₑ-assign L⇓a† M⇓V†) =
  case determinism L⇓a L⇓a† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
determinism (⇓ₑ-assign L⇓a _) (⇓ₑ-assign-● L⇓● _) =
  contradiction (determinism L⇓a L⇓●) (λ ())
determinism (⇓ₑ-assign-● L⇓● _) (⇓ₑ-assign L⇓a _) =
  contradiction (determinism L⇓● L⇓a) (λ ())
determinism (⇓ₑ-assign-● L⇓● M⇓V) (⇓ₑ-assign-● L⇓●† M⇓V†) =
  case determinism L⇓● L⇓●† of λ where
  ⟨ refl , refl ⟩ →
    case determinism M⇓V M⇓V† of λ where
    ⟨ refl , refl ⟩ → ⟨ refl , refl ⟩
