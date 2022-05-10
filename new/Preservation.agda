open import Data.Nat
open import Data.List

open import Syntax
-- open import GenericSubstitution

open import Types
open import CC

module Preservation where

_⦂_⇒_ : Rename → List Type → List Type → Set
ρ ⦂ Γ ⇒ Δ = ∀ {x A} → Γ ∋ x ⦂ A → Δ ∋ ρ x ⦂ A

ext-pres : ∀ {Γ Δ ρ A}
  → ρ ⦂ Γ ⇒ Δ
  → ext ρ ⦂ (A ∷ Γ) ⇒ (A ∷ Δ)
ext-pres ⊢ρ {0} eq = eq
ext-pres ⊢ρ {suc x} Γ∋x = ⊢ρ Γ∋x

rename-pres : ∀ {Γ Δ : Context} {Σ gc pc A M ρ}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ A
  → ρ ⦂ Γ ⇒ Δ
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
rename-pres (⊢cast ⊢M) ⊢ρ = ⊢cast (rename-pres ⊢M ⊢ρ)
rename-pres (⊢ref ⊢M) ⊢ρ = ⊢ref (rename-pres ⊢M ⊢ρ)
rename-pres (⊢deref ⊢M) ⊢ρ = ⊢deref (rename-pres ⊢M ⊢ρ)
rename-pres (⊢assign ⊢L ⊢M) ⊢ρ = ⊢assign (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢nsu-ref ⊢M) ⊢ρ = ⊢nsu-ref (rename-pres ⊢M ⊢ρ)
rename-pres (⊢nsu-assign ⊢L ⊢M) ⊢ρ = ⊢nsu-assign (rename-pres ⊢L ⊢ρ) (rename-pres ⊢M ⊢ρ)
rename-pres (⊢prot ⊢M) ⊢ρ = ⊢prot (rename-pres ⊢M ⊢ρ)
rename-pres (⊢inj-pc ⊢M) ⊢ρ = ⊢inj-pc (rename-pres ⊢M ⊢ρ)
rename-pres (⊢proj-pc ⊢M pc≼ℓ) ⊢ρ = ⊢proj-pc (rename-pres ⊢M ⊢ρ) pc≼ℓ
rename-pres ⊢err ⊢ρ = ⊢err
rename-pres (⊢sub ⊢M A<:B) ⊢ρ = ⊢sub (rename-pres ⊢M ⊢ρ) A<:B
rename-pres (⊢sub-pc ⊢M gc<:gc′) ⊢ρ = ⊢sub-pc (rename-pres ⊢M ⊢ρ) gc<:gc′

rename-↑1-pres : ∀ {Γ Σ gc pc M A B}
  → Γ ; Σ ; gc ; pc ⊢ M ⦂ B
  → (A ∷ Γ) ; Σ ; gc ; pc ⊢ rename (↑ 1) M ⦂ B
rename-↑1-pres ⊢M = rename-pres ⊢M (λ {x} {A} Γ∋x → Γ∋x)
