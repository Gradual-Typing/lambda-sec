open import Data.Nat
open import Data.List
open import Function using (case_of_)

open import Syntax

open import Types
open import CC

module Preservation where

Rename_⦂_⇒_ : Rename → List Type → List Type → Set
Rename ρ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A

ext-pres : ∀ {Γ Δ ρ A}
  → Rename ρ ⦂ Γ ⇒ Δ
  → Rename ext ρ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-pres ⊢ρ {0} eq = eq
ext-pres ⊢ρ {suc x} Γ∋x = ⊢ρ Γ∋x

rename-pres : ∀ {Γ Δ : Context} {Σ gc pc A M ρ}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  → Rename ρ ⦂ Γ ⇒ Δ
    -----------------------------
  → Δ ; Σ ; gc ; pc ⊢ rename ρ M ⦂ A
rename-pres ⊢const ⊢ρ = ⊢const
rename-pres (⊢addr eq) ⊢ρ = ⊢addr eq
rename-pres (⊢var Γ∋x) ⊢ρ = ⊢var (⊢ρ Γ∋x)
rename-pres {Γ} {Δ} (⊢lam ⊢N) ⊢ρ =
  ⊢lam (rename-pres ⊢N (λ {x} {A} → ext-pres {Γ} {Δ} ⊢ρ {x} {A}))
rename-pres (⊢app ⊢L ⊢M) ⊢ρ = ⊢app (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢if ⊢L ⊢M ⊢N) ⊢ρ =
  ⊢if (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) (rename-pres ⊢N ⊢ρ)
rename-pres {Γ} {Δ} (⊢let ⊢M ⊢N) ⊢ρ =
  ⊢let (rename-pres ⊢M ⊢ρ) (rename-pres ⊢N (λ {x} {A} → ext-pres {Γ} {Δ} ⊢ρ {x} {A}))
rename-pres (⊢ref ⊢M pc′≼ℓ) ⊢ρ = ⊢ref (rename-pres ⊢M ⊢ρ) pc′≼ℓ
rename-pres (⊢ref? ⊢M) ⊢ρ = ⊢ref? (rename-pres ⊢M ⊢ρ)
rename-pres (⊢ref✓ ⊢M pc≼ℓ) ⊢ρ = ⊢ref✓ (rename-pres ⊢M ⊢ρ) pc≼ℓ
rename-pres (⊢deref ⊢M) ⊢ρ = ⊢deref (rename-pres ⊢M ⊢ρ)
rename-pres (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢ρ = ⊢assign (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) pc′≼ℓ
rename-pres (⊢assign? ⊢L ⊢M) ⊢ρ = ⊢assign? (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢assign✓ ⊢L ⊢M pc≼ℓ) ⊢ρ = ⊢assign✓ (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ) pc≼ℓ
rename-pres (⊢prot ⊢M) ⊢ρ = ⊢prot (rename-pres ⊢M ⊢ρ)
rename-pres (⊢cast ⊢M) ⊢ρ = ⊢cast (rename-pres ⊢M ⊢ρ)
rename-pres (⊢cast-pc ⊢M pc~g) ⊢ρ = ⊢cast-pc (rename-pres ⊢M ⊢ρ) pc~g
rename-pres ⊢err ⊢ρ = ⊢err
rename-pres (⊢sub ⊢M A<:B) ⊢ρ = ⊢sub (rename-pres ⊢M ⊢ρ) A<:B
rename-pres (⊢sub-pc ⊢M gc<:gc′) ⊢ρ = ⊢sub-pc (rename-pres ⊢M ⊢ρ) gc<:gc′

rename-↑1-pres : ∀ {Γ Σ gc pc M A B}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ B
  → (A ∷ Γ) ; Σ ; gc ; pc ⊢ rename (↑ 1) M ⦂ B
rename-↑1-pres ⊢M = rename-pres ⊢M (λ {x} {A} Γ∋x → Γ∋x)

Subst_⦂_⇒_ : Subst → List Type → List Type → Set
Subst σ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → (∀ {Σ gc pc} → Δ ; Σ ; gc ; pc ⊢ σ x ⦂ A)

exts-pres : ∀ {Γ Δ σ A}
  → Subst σ ⦂ Γ ⇒ Δ
  → Subst ext σ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
exts-pres ⊢σ {0} eq = (⊢var eq)
exts-pres ⊢σ {suc x} Γ∋x = rename-↑1-pres (⊢σ Γ∋x)

subst-pres : ∀ {Γ Δ : Context} {Σ gc pc A M σ}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  → Subst σ ⦂ Γ ⇒ Δ
    -----------------------------
  → Δ ; Σ ; gc ; pc ⊢ ⟪ σ ⟫ M ⦂ A
subst-pres ⊢const ⊢σ = ⊢const
subst-pres (⊢addr eq) ⊢σ = ⊢addr eq
subst-pres (⊢var Γ∋x) ⊢σ = ⊢σ Γ∋x
subst-pres {Γ} {Δ} (⊢lam ⊢N) ⊢σ =
  ⊢lam (subst-pres ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σ {x} {A}))
subst-pres (⊢app ⊢L ⊢M) ⊢σ = ⊢app (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ)
subst-pres (⊢if ⊢L ⊢M ⊢N) ⊢σ =
  ⊢if (subst-pres ⊢L ⊢σ) (subst-pres ⊢M ⊢σ) (subst-pres ⊢N ⊢σ)
subst-pres {Γ} {Δ} (⊢let ⊢M ⊢N) ⊢σ =
  ⊢let (subst-pres ⊢M ⊢σ) (subst-pres ⊢N (λ {x} {A} → exts-pres {Γ} {Δ} ⊢σ {x} {A}))
subst-pres (⊢ref ⊢M pc′≼ℓ) ⊢ρ = ⊢ref (subst-pres ⊢M ⊢ρ) pc′≼ℓ
subst-pres (⊢ref? ⊢M) ⊢ρ = ⊢ref? (subst-pres ⊢M ⊢ρ)
subst-pres (⊢ref✓ ⊢M pc≼ℓ) ⊢ρ = ⊢ref✓ (subst-pres ⊢M ⊢ρ) pc≼ℓ
subst-pres (⊢deref ⊢M) ⊢ρ = ⊢deref (subst-pres ⊢M ⊢ρ)
subst-pres (⊢assign ⊢L ⊢M pc′≼ℓ) ⊢ρ = ⊢assign (subst-pres ⊢L ⊢ρ) (subst-pres ⊢M ⊢ρ) pc′≼ℓ
subst-pres (⊢assign? ⊢L ⊢M) ⊢ρ = ⊢assign? (subst-pres ⊢L ⊢ρ) (subst-pres ⊢M ⊢ρ)
subst-pres (⊢assign✓ ⊢L ⊢M pc≼ℓ) ⊢ρ = ⊢assign✓ (subst-pres ⊢L ⊢ρ) (subst-pres ⊢M ⊢ρ) pc≼ℓ
subst-pres (⊢prot ⊢M) ⊢ρ = ⊢prot (subst-pres ⊢M ⊢ρ)
subst-pres (⊢cast ⊢M) ⊢ρ = ⊢cast (subst-pres ⊢M ⊢ρ)
subst-pres (⊢cast-pc ⊢M pc~g) ⊢ρ = ⊢cast-pc (subst-pres ⊢M ⊢ρ) pc~g
subst-pres ⊢err ⊢ρ = ⊢err
subst-pres (⊢sub ⊢M A<:B) ⊢ρ = ⊢sub (subst-pres ⊢M ⊢ρ) A<:B
subst-pres (⊢sub-pc ⊢M gc<:gc′) ⊢ρ = ⊢sub-pc (subst-pres ⊢M ⊢ρ) gc<:gc′
