module BigStep where

open import Statics
open Context


-- we first define substitution
-- extension lemma
ext : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ∋ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ∋ A)
ext ρ Z      =  Z
ext ρ (S x)  =  S (ρ x)

-- renaming
rename : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ∋ A)
    -----------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
rename ρ (` x)                  =  ` (ρ x)
rename ρ (val (ƛ N / 𝓁))        =  val ( ƛ (rename (ext ρ) N) / 𝓁 )
rename ρ (val (`true/ 𝓁))       =  val (`true/ 𝓁)
rename ρ (val (`false/ 𝓁))      =  val (`false/ 𝓁)
rename ρ (L · M)                =  (rename ρ L) · (rename ρ M)
rename ρ (if L M N)             =  if (rename ρ L) (rename ρ M) (rename ρ N)
rename ρ (M `∧ N)               =  (rename ρ M) `∧ (rename ρ N)
rename ρ (M `∨ N)               =  (rename ρ M) `∨ (rename ρ N)
rename ρ (sub M ⊢≤)             =  sub (rename ρ M) ⊢≤

-- extension (in terms of well-formedness)
exts : ∀ {Γ Δ}
  → (∀ {A} →       Γ ∋ A →     Δ ⊢ₑ A)
    ---------------------------------
  → (∀ {A B} → Γ , B ∋ A → Δ , B ⊢ₑ A)
exts σ Z      =  ` Z
exts σ (S x)  =  rename S_ (σ x)

-- substitution
subst : ∀ {Γ Δ}
  → (∀ {A} → Γ ∋ A → Δ ⊢ₑ A)
    -----------------------
  → (∀ {A} → Γ ⊢ₑ A → Δ ⊢ₑ A)
subst σ (` k)          =  σ k
subst σ (val (ƛ N / 𝓁))      =  val (ƛ (subst (exts σ) N) / 𝓁)
subst σ (val (`true/ 𝓁))     =  val (`true/ 𝓁)
subst σ (val (`false/ 𝓁))    =  val (`false/ 𝓁)
subst σ (L · M)              =  (subst σ L) · (subst σ M)
subst σ (if L M N)           =  if (subst σ L) (subst σ M) (subst σ N)
subst σ (M `∧ N)             =  (subst σ M) `∧ (subst σ N)
subst σ (M `∨ N)             =  (subst σ M) `∨ (subst σ N)
subst σ (sub M ⊢≤)           =  sub (subst σ M) ⊢≤

_[_] : ∀ {Γ A B}
        → Γ , B ⊢ₑ A
        → Γ ⊢ₑ B
          ---------
        → Γ ⊢ₑ A
_[_] {Γ} {A} {B} N M =  subst {Γ , B} {Γ} σ {A} N
  where
  σ : ∀ {A} → Γ , B ∋ A → Γ ⊢ₑ A
  σ Z      =  M
  σ (S x)  =  ` x

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
  ⇓-val : ∀ {A} {V : ∅ ⊢ᵥ A}
        --------------
        → (val V) ⇓ V  -- simply get rid of the `val`

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

  ⇓-cond₁ : ∀ {𝓁ₗ A Vₘ} {L : ∅ ⊢ₑ `𝔹 / 𝓁ₗ} {M : ∅ ⊢ₑ A ⊔ₛ 𝓁ₗ} {N : ∅ ⊢ₑ A ⊔ₛ 𝓁ₗ}
      → L ⇓ (`true/ 𝓁ₗ)
      → M ⇓ Vₘ
        ------------------------
      → if L M N ⇓ Vₘ  -- note that `Vₘ` already inhebits type `A ⊔ₛ 𝓁ₗ`

  ⇓-cond₂ : ∀ {𝓁ₗ A Vₙ} {L : ∅ ⊢ₑ `𝔹 / 𝓁ₗ} {M : ∅ ⊢ₑ A ⊔ₛ 𝓁ₗ} {N : ∅ ⊢ₑ A ⊔ₛ 𝓁ₗ}
      → L ⇓ (`false/ 𝓁ₗ)
      → N ⇓ Vₙ
        ------------------------
      → if L M N ⇓ Vₙ  -- note that `Vₙ` already inhebits type `A ⊔ₛ 𝓁ₗ`

  ⇓-app : ∀ {𝓁ₘ A B Vₙ V M′} {M : ∅ ⊢ₑ (A ⇒ B) / 𝓁ₘ} {N : ∅ ⊢ₑ A}
      → M ⇓ (ƛ M′ / 𝓁ₘ)
      → N ⇓ Vₙ
      → (M′ [ (val Vₙ) ]) ⇓ V
        ------------------------
      → (M · N) ⇓ (V ⊔ᵥ 𝓁ₘ)
