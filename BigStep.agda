module BigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Statics


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



_/_⦂_≈ᵥ⦅_⦆_ : (t : 𝕋) → (𝓁 : ℒ) → (v₁ : ∅ ⊢ᵥ (t / 𝓁)) → (ζ : ℒ) → (v₂ : ∅ ⊢ᵥ (t / 𝓁)) → Set
_/_⦂_≈ₑ⦅_⦆_ : (t : 𝕋) → (𝓁 : ℒ) → (e₁ : ∅ ⊢ₑ (t / 𝓁)) → (ζ : ℒ) → (e₂ : ∅ ⊢ₑ (t / 𝓁)) → Set

`𝔹 / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ = 𝓁 ⊑ ζ → v₁ ≡ v₂
((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)) / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ =
    𝓁 ⊑ ζ
  → (∀ {v₁′ v₂′}
       → t₁ / 𝓁₁ ⦂ v₁′ ≈ᵥ⦅ ζ ⦆ v₂′
       → t₂ / 𝓁₂ ⊔ 𝓁 ⦂ ((val v₁) · (val v₁′)) ≈ₑ⦅ ζ ⦆ ((val v₂) · (val v₂′)))

t / 𝓁 ⦂ e₁ ≈ₑ⦅ ζ ⦆ e₂ =
  (∀ {v₁ v₂}
    → e₁ ⇓ v₁
    → e₂ ⇓ v₂
    → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂)


-- fundamental property
-- first we define related substitutions under a typing context Γ
_⊢_≈ₛ⦅_⦆_ : ∀ Γ → (∀ {A} → Γ ∋ A → ∅ ⊢ₑ A) → ℒ → (∀ {A} → Γ ∋ A → ∅ ⊢ₑ A) → Set
Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂ = ∀ {t 𝓁} {x : Γ ∋ (t / 𝓁)} → t / 𝓁 ⦂ (σ₁ x) ≈ₑ⦅ ζ ⦆ (σ₂ x)

⇓≡ : ∀ {s v v₁ v₂} → (_⇓_ {s} (val v) v₁) → (_⇓_ {s} (val v) v₂) → v₁ ≡ v₂
⇓≡ ⇓-val ⇓-val = refl

-- If Γ ⊢ e : s and Γ ⊢ σ₁ ≈ζ σ₂ then σ₁(e) ≈ζ σ₂(e) : s
fundamental : ∀ {Γ t 𝓁 ζ}
  → (σ₁ : (∀ {A} → Γ ∋ A → ∅ ⊢ₑ A))
  → (σ₂ : (∀ {A} → Γ ∋ A → ∅ ⊢ₑ A))
  → (e : Γ ⊢ₑ t / 𝓁)
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    -----------------------------------------------
  → t / 𝓁 ⦂ (subst σ₁ e) ≈ₑ⦅ ζ ⦆ (subst σ₂ e)
fundamental σ₁ σ₂ (` x) σ₁≈σ₂ = σ₁≈σ₂
fundamental σ₁ σ₂ (val v) σ₁≈σ₂ with v
... | `true/ 𝓁 = λ ⇓v₁ ⇓v₂ 𝓁⊑ζ → ⇓≡ ⇓v₁ ⇓v₂
... | `false/ 𝓁 = λ ⇓v₁ ⇓v₂ 𝓁⊑ζ → ⇓≡ ⇓v₁ ⇓v₂
... | ƛ N / 𝓁 = λ ⇓v₁ ⇓v₂ → {!!}
fundamental σ₁ σ₂ (e `∧ e₁) σ₁≈σ₂ = {!!}
fundamental σ₁ σ₂ (e `∨ e₁) σ₁≈σ₂ = {!!}
fundamental σ₁ σ₂ (e · e₁) σ₁≈σ₂ = {!!}
fundamental σ₁ σ₂ (if e e₁ e₂) σ₁≈σ₂ = {!!}
fundamental σ₁ σ₂ (sub e x) σ₁≈σ₂ = {!!}


record _⇔_ (A B : Set) : Set where
  field
    to   : A → B
    from : B → A

-- properties
-- non-interference of λ-sec
-- non-interference : ∀ {t V}
--   → (M : ∅ , (t / 𝐻) ⊢ₑ `𝔹 / 𝐿)
--   → (V₁ : ∅ ⊢ᵥ (t / 𝐻))
--   → (V₂ : ∅ ⊢ᵥ (t / 𝐻))
--     -----------------------------------------------
--   → ((M [ (val V₁) ]) ⇓ V) ⇔ ((M [ (val V₂) ]) ⇓ V)
-- non-interference {t} {V} M V₁ V₂ = record { to = {!!} ; from = {!!} }
