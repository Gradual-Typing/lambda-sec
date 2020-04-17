module BigStep where

open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_⊔_ to _⊔ₙ_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)

open import Statics



Rename : Context → Context → Set
Rename Γ Δ = ∀ {X} → Γ ∋ X → Δ ∋ X

Subst : Context → Context → Set
Subst Γ Δ = ∀ {X} → Γ ∋ X → Δ ⊢ₑ X

-- we first define substitution
-- extension lemma
ext : ∀ {Γ Δ A}
  → Rename Γ Δ
    ---------------------------------
  → Rename (Γ , A) (Δ , A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

-- renaming
renameᵥ : ∀ {Γ Δ}
  → Rename Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ᵥ A → Δ ⊢ᵥ A)
renameₑ : ∀ {Γ Δ}
  → Rename Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
renameᵥ ρ (ƛ N / 𝓁)            = ƛ (renameₑ (ext ρ) N) / 𝓁
renameᵥ ρ (`true/ 𝓁)           = `true/ 𝓁
renameᵥ ρ (`false/ 𝓁)          = `false/ 𝓁
renameₑ ρ (` x)                =  ` (ρ x)
renameₑ ρ (val v)              =  val (renameᵥ ρ v)
renameₑ ρ (L · M)              =  (renameₑ ρ L) · (renameₑ ρ M)
renameₑ ρ (if L M N)           =  if (renameₑ ρ L) (renameₑ ρ M) (renameₑ ρ N)
renameₑ ρ (M `∧ N)             =  (renameₑ ρ M) `∧ (renameₑ ρ N)
renameₑ ρ (M `∨ N)             =  (renameₑ ρ M) `∨ (renameₑ ρ N)
renameₑ ρ (sub M ⊢≤)           =  sub (renameₑ ρ M) ⊢≤

-- extension (in terms of well-formedness)
exts : ∀ {Γ Δ A}
  → Subst Γ Δ
    ---------------------------------
  → Subst (Γ , A) (Δ , A)
exts σ Z      =  ` Z
exts σ (S x)  =  renameₑ S_ (σ x)

-- substitution
substᵥ : ∀ {Γ Δ}
  → Subst Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ᵥ A → Δ ⊢ᵥ A)
substₑ : ∀ {Γ Δ}
  → Subst Γ Δ
    -----------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
substᵥ σ (ƛ N / 𝓁)          = ƛ (substₑ (exts σ) N) / 𝓁
substᵥ σ (`true/ 𝓁)         = `true/ 𝓁
substᵥ σ (`false/ 𝓁)        = `false/ 𝓁
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

subst-dist-∧ : ∀ {Γ Δ 𝓁₁ 𝓁₂}
  → (σ : Subst Γ Δ)
  → (M : Γ ⊢ₑ `𝔹 / 𝓁₁)
  → (N : Γ ⊢ₑ `𝔹 / 𝓁₂)
  → substₑ σ (M `∧ N) ≡ (substₑ σ M) `∧ (substₑ σ N)
subst-dist-∧ σ M N = refl

subst-dist-· : ∀ {Γ Δ t₁ t₂ 𝓁₁ 𝓁₂ 𝓁}
  → (σ : Subst Γ Δ)
  → (M : Γ ⊢ₑ ((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)) / 𝓁)
  → (N : Γ ⊢ₑ (t₁ / 𝓁₁))
  → substₑ σ (M · N) ≡ (substₑ σ M) · (substₑ σ N)
subst-dist-· σ M N = refl


_⟦∧⟧_ : ∀ {𝓁ₘ 𝓁ₙ}
      → (M : ∅ ⊢ᵥ `𝔹 / 𝓁ₘ)
      → (N : ∅ ⊢ᵥ `𝔹 / 𝓁ₙ)
        -----------------------
      → ∅ ⊢ᵥ `𝔹 / (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∧⟧_ {𝓁ₘ} {𝓁ₙ} (`true/ 𝓁ₘ)  (`true/ 𝓁ₙ)   = `true/  (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∧⟧_ {𝓁ₘ} {𝓁ₙ} (`true/ 𝓁ₘ)  (`false/ 𝓁ₙ)  = `false/ (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∧⟧_ {𝓁ₘ} {𝓁ₙ} (`false/ 𝓁ₘ) (`true/ 𝓁ₙ)   = `false/ (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∧⟧_ {𝓁ₘ} {𝓁ₙ} (`false/ 𝓁ₘ) (`false/ 𝓁ₙ)  = `false/ (𝓁ₘ ⊔ 𝓁ₙ)

_⟦∨⟧_ : ∀ {𝓁ₘ 𝓁ₙ}
      → (M : ∅ ⊢ᵥ `𝔹 / 𝓁ₘ)
      → (N : ∅ ⊢ᵥ `𝔹 / 𝓁ₙ)
        -----------------------
      → ∅ ⊢ᵥ `𝔹 / (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∨⟧_ {𝓁ₘ} {𝓁ₙ} (`true/ 𝓁ₘ)  (`true/ 𝓁ₙ)   = `true/  (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∨⟧_ {𝓁ₘ} {𝓁ₙ} (`true/ 𝓁ₘ)  (`false/ 𝓁ₙ)  = `true/  (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∨⟧_ {𝓁ₘ} {𝓁ₙ} (`false/ 𝓁ₘ) (`true/ 𝓁ₙ)   = `true/  (𝓁ₘ ⊔ 𝓁ₙ)
_⟦∨⟧_ {𝓁ₘ} {𝓁ₙ} (`false/ 𝓁ₘ) (`false/ 𝓁ₙ)  = `false/ (𝓁ₘ ⊔ 𝓁ₙ)


data _⇓_ : ∀ {A} → ∅ ⊢ₑ A → ∅ ⊢ᵥ A → Set where -- only run on closed terms

  -- v ⇓ v
  ⇓-val : ∀ {A} {v : ∅ ⊢ᵥ A}
        --------------
        → (val v) ⇓ v  -- simply get rid of the `val`

  -- binops
  ⇓-∧ : ∀ {𝓁ₘ 𝓁ₙ Vₘ Vₙ} {M : ∅ ⊢ₑ `𝔹 / 𝓁ₘ} {N : ∅ ⊢ₑ `𝔹 / 𝓁ₙ}
      → M ⇓ Vₘ
      → N ⇓ Vₙ
        ------------------------
      → (M `∧ N) ⇓ (Vₘ ⟦∧⟧ Vₙ)

  ⇓-∨ : ∀ {𝓁ₘ 𝓁ₙ Vₘ Vₙ} {M : ∅ ⊢ₑ `𝔹 / 𝓁ₘ} {N : ∅ ⊢ₑ `𝔹 / 𝓁ₙ}
      → M ⇓ Vₘ
      → N ⇓ Vₙ
        ------------------------
      → (M `∨ N) ⇓ (Vₘ ⟦∨⟧ Vₙ)

  ⇓-cond₁ : ∀ {t 𝓁ₗ 𝓁 Vₘ} {L : ∅ ⊢ₑ `𝔹 / 𝓁ₗ} {M : ∅ ⊢ₑ t / (𝓁 ⊔ 𝓁ₗ)} {N : ∅ ⊢ₑ t / (𝓁 ⊔ 𝓁ₗ)}
      → L ⇓ (`true/ 𝓁ₗ)
      → M ⇓ Vₘ
        ------------------------
      → if L M N ⇓ Vₘ  -- note that `Vₘ` already inhebits type `A ⊔ₛ 𝓁ₗ`

  ⇓-cond₂ : ∀ {t 𝓁ₗ 𝓁 Vₙ} {L : ∅ ⊢ₑ `𝔹 / 𝓁ₗ} {M : ∅ ⊢ₑ t / (𝓁 ⊔ 𝓁ₗ)} {N : ∅ ⊢ₑ t / (𝓁 ⊔ 𝓁ₗ)}
      → L ⇓ (`false/ 𝓁ₗ)
      → N ⇓ Vₙ
        ------------------------
      → if L M N ⇓ Vₙ  -- note that `Vₙ` already inhebits type `A ⊔ₛ 𝓁ₗ`

  ⇓-app : ∀ {t₁ t₂ 𝓁₁ 𝓁₂ 𝓁 Vₙ V M′} {M : ∅ ⊢ₑ ((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)) / 𝓁} {N : ∅ ⊢ₑ t₁ / 𝓁₁}
      → M ⇓ (ƛ M′ / 𝓁)
      → N ⇓ Vₙ
      → (M′ [ (val Vₙ) ]) ⇓ V
        ------------------------
      → (M · N) ⇓ (V ⊔ᵥ 𝓁)
