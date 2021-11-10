module BigStep where

open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_⊔_ to _⊔ₙ_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)

open import Statics


Rename : Context → Context → Set
Rename Γ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X

Subst : Context → Context → Set
Subst Γ Δ = ∀ {X} → Γ ∋ X → Δ ⊢ₑ X

ext : ∀ {Γ Δ A}
  → Rename Γ Δ
    ---------------------------------
  → Rename (Γ , A) (Δ , A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

renameᵥ : ∀ {Γ Δ}
  → Rename Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ᵥ A → Δ ⊢ᵥ A)
renameₑ : ∀ {Γ Δ}
  → Rename Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
renameᵥ ρ (ƛ N / ℓ)            = ƛ (renameₑ (ext ρ) N) / ℓ
renameᵥ ρ (`true/ ℓ)           = `true/ ℓ
renameᵥ ρ (`false/ ℓ)          = `false/ ℓ
renameₑ ρ (` x)                =  ` (ρ x)
renameₑ ρ (val v)              =  val (renameᵥ ρ v)
renameₑ ρ (L · M)              =  (renameₑ ρ L) · (renameₑ ρ M)
renameₑ ρ (if L M N)           =  if (renameₑ ρ L) (renameₑ ρ M) (renameₑ ρ N)
renameₑ ρ (M `∧ N)             =  (renameₑ ρ M) `∧ (renameₑ ρ N)
renameₑ ρ (M `∨ N)             =  (renameₑ ρ M) `∨ (renameₑ ρ N)
renameₑ ρ (sub M ⊢≤)           =  sub (renameₑ ρ M) ⊢≤

exts : ∀ {Γ Δ A}
  → Subst Γ Δ
    ----------------------
  → Subst (Γ , A) (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  renameₑ S_ (σ x)

substᵥ : ∀ {Γ Δ}
  → Subst Γ Δ
    ----------------------------
  → (∀ {A} → Γ ⊢ᵥ A → Δ ⊢ᵥ A)
substₑ : ∀ {Γ Δ}
  → Subst Γ Δ
    ----------------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
substᵥ σ (ƛ N / ℓ)          = ƛ (substₑ (exts σ) N) / ℓ
substᵥ σ (`true/ ℓ)         = `true/ ℓ
substᵥ σ (`false/ ℓ)        = `false/ ℓ
substₑ σ (` k)              =  σ k
substₑ σ (val v)            =  val (substᵥ σ v)
substₑ σ (L · M)            =  (substₑ σ L) · (substₑ σ M)
substₑ σ (if L M N)         =  if (substₑ σ L) (substₑ σ M) (substₑ σ N)
substₑ σ (M `∧ N)           =  (substₑ σ M) `∧ (substₑ σ N)
substₑ σ (M `∨ N)           =  (substₑ σ M) `∨ (substₑ σ N)
substₑ σ (sub M ⊢≤)         =  sub (substₑ σ M) ⊢≤

_•_ : ∀ {Γ Δ A}
  → Subst Γ Δ
  → Δ ⊢ₑ A
  → Subst (Γ , A) Δ
_•_ σ M Z = M
_•_ σ M (S x) = σ x

σ₀ : ∀ {Γ A} → Γ ⊢ₑ A → Subst (Γ , A) Γ
σ₀ M Z      =  M
σ₀ M (S x)  =  ` x

_[_] : ∀ {Γ A B}
  → Γ , A ⊢ₑ B
  → Γ ⊢ₑ A
    ---------
  → Γ ⊢ₑ B
_[_] {Γ} {A} {B} N M =  substₑ {Γ , A} {Γ} (σ₀ M) N

subst-dist-∧ : ∀ {Γ Δ ℓ₁ ℓ₂}
  → (σ : Subst Γ Δ)
  → (M : Γ ⊢ₑ `𝔹 / ℓ₁)
  → (N : Γ ⊢ₑ `𝔹 / ℓ₂)
  → substₑ σ (M `∧ N) ≡ (substₑ σ M) `∧ (substₑ σ N)
subst-dist-∧ σ M N = refl

subst-dist-· : ∀ {Γ Δ t₁ t₂ ℓ₁ ℓ₂ ℓ}
  → (σ : Subst Γ Δ)
  → (M : Γ ⊢ₑ ((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)) / ℓ)
  → (N : Γ ⊢ₑ (t₁ / ℓ₁))
  → substₑ σ (M · N) ≡ (substₑ σ M) · (substₑ σ N)
subst-dist-· σ M N = refl


_⟦∧⟧_ : ∀ {ℓₘ ℓₙ}
      → (M : ∅ ⊢ᵥ `𝔹 / ℓₘ)
      → (N : ∅ ⊢ᵥ `𝔹 / ℓₙ)
        -----------------------
      → ∅ ⊢ᵥ `𝔹 / (ℓₘ ⊔ ℓₙ)
_⟦∧⟧_ {ℓₘ} {ℓₙ} (`true/ ℓₘ)  (`true/ ℓₙ)   = `true/  (ℓₘ ⊔ ℓₙ)
_⟦∧⟧_ {ℓₘ} {ℓₙ} (`true/ ℓₘ)  (`false/ ℓₙ)  = `false/ (ℓₘ ⊔ ℓₙ)
_⟦∧⟧_ {ℓₘ} {ℓₙ} (`false/ ℓₘ) (`true/ ℓₙ)   = `false/ (ℓₘ ⊔ ℓₙ)
_⟦∧⟧_ {ℓₘ} {ℓₙ} (`false/ ℓₘ) (`false/ ℓₙ)  = `false/ (ℓₘ ⊔ ℓₙ)

_⟦∨⟧_ : ∀ {ℓₘ ℓₙ}
      → (M : ∅ ⊢ᵥ `𝔹 / ℓₘ)
      → (N : ∅ ⊢ᵥ `𝔹 / ℓₙ)
        -----------------------
      → ∅ ⊢ᵥ `𝔹 / (ℓₘ ⊔ ℓₙ)
_⟦∨⟧_ {ℓₘ} {ℓₙ} (`true/ ℓₘ)  (`true/ ℓₙ)   = `true/  (ℓₘ ⊔ ℓₙ)
_⟦∨⟧_ {ℓₘ} {ℓₙ} (`true/ ℓₘ)  (`false/ ℓₙ)  = `true/  (ℓₘ ⊔ ℓₙ)
_⟦∨⟧_ {ℓₘ} {ℓₙ} (`false/ ℓₘ) (`true/ ℓₙ)   = `true/  (ℓₘ ⊔ ℓₙ)
_⟦∨⟧_ {ℓₘ} {ℓₙ} (`false/ ℓₘ) (`false/ ℓₙ)  = `false/ (ℓₘ ⊔ ℓₙ)


data _⇓_ : ∀ {A} → ∅ ⊢ₑ A → ∅ ⊢ᵥ A → Set where -- only run on closed terms

  ⇓-val : ∀ {A} {v : ∅ ⊢ᵥ A}
        ---------------
        → (val v) ⇓ v

  ⇓-∧ : ∀ {ℓₘ ℓₙ Vₘ Vₙ} {M : ∅ ⊢ₑ `𝔹 / ℓₘ} {N : ∅ ⊢ₑ `𝔹 / ℓₙ}
      → M ⇓ Vₘ
      → N ⇓ Vₙ
        ------------------------
      → (M `∧ N) ⇓ (Vₘ ⟦∧⟧ Vₙ)

  ⇓-∨ : ∀ {ℓₘ ℓₙ Vₘ Vₙ} {M : ∅ ⊢ₑ `𝔹 / ℓₘ} {N : ∅ ⊢ₑ `𝔹 / ℓₙ}
      → M ⇓ Vₘ
      → N ⇓ Vₙ
        ------------------------
      → (M `∨ N) ⇓ (Vₘ ⟦∨⟧ Vₙ)

  ⇓-cond₁ : ∀ {t ℓₗ ℓ Vₘ} {L : ∅ ⊢ₑ `𝔹 / ℓₗ} {M : ∅ ⊢ₑ t / (ℓ ⊔ ℓₗ)} {N : ∅ ⊢ₑ t / (ℓ ⊔ ℓₗ)}
      → L ⇓ (`true/ ℓₗ)
      → M ⇓ Vₘ
        ------------------------
      → if L M N ⇓ Vₘ  {- Note `Vₘ` inhabits `A ⊔ₛ ℓₗ` -}

  ⇓-cond₂ : ∀ {t ℓₗ ℓ Vₙ} {L : ∅ ⊢ₑ `𝔹 / ℓₗ} {M : ∅ ⊢ₑ t / (ℓ ⊔ ℓₗ)} {N : ∅ ⊢ₑ t / (ℓ ⊔ ℓₗ)}
      → L ⇓ (`false/ ℓₗ)
      → N ⇓ Vₙ
        ------------------------
      → if L M N ⇓ Vₙ  {- Note `Vₙ` inhabits `A ⊔ₛ ℓₗ` -}

  ⇓-app : ∀ {t₁ t₂ ℓ₁ ℓ₂ ℓ Vₙ V M′} {M : ∅ ⊢ₑ ((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)) / ℓ} {N : ∅ ⊢ₑ t₁ / ℓ₁}
      → M ⇓ (ƛ M′ / ℓ)
      → N ⇓ Vₙ
      → (M′ [ (val Vₙ) ]) ⇓ V
        ------------------------
      → (M · N) ⇓ (V ⊔ᵥ ℓ)
