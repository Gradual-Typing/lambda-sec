module BigStep where

open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
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

rename-ext : ∀ {Γ A B}
  → (M : Γ ⊢ₑ B)
  → (N : Γ ⊢ₑ A)
  → (renameₑ S_ M) [ N ] ≡ M
rename-ext {Γ} {A} {B} (` x) N = refl
rename-ext {Γ} {A} {B} (val x) N = {!!}
rename-ext (M₁ `∧ M₂) N rewrite subst-dist-∧ (σ₀ N) (renameₑ S_ M₁) (renameₑ S_ M₂) | rename-ext M₁ N | rename-ext M₂ N = refl
rename-ext (M₁ `∨ M₂) N = {!!}
rename-ext (M₁ · M₂) N rewrite subst-dist-· (σ₀ N) (renameₑ S_ M₁) (renameₑ S_ M₂) | rename-ext M₁ N | rename-ext M₂ N = refl
rename-ext {Γ} {A} {.(_ / (_ ⊔ _))} (if M M₁ M₂) N = {!!}
rename-ext {Γ} {A} {B} (sub M x) N = {!!}


postulate
  subst-ext : ∀ {Γ Δ A A′}
    → (σ : Subst Γ Δ)
    → (M : Γ , A′ ⊢ₑ A)
    → (N : Δ ⊢ₑ A′)
    → (substₑ (exts σ) M) [ N ] ≡ substₑ (σ • N) M
-- subst-ext σ (` Z) N = refl
-- subst-ext σ (` (S x)) N = {!!}
-- subst-ext σ (val x) N = {!!}
-- subst-ext σ (M `∧ M₁) N = {!!}
-- subst-ext σ (M `∨ M₁) N = {!!}
-- subst-ext σ (M · M₁) N = {!!}
-- subst-ext σ (if M M₁ M₂) N = {!!}
-- subst-ext σ (sub M x) N = {!!}

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

-- data _⦂_≈ᵥ⦅_⦆_ : (s : 𝕊) → (v₁ : ∅ ⊢ᵥ s) → (ζ : ℒ) → (v₂ : ∅ ⊢ᵥ s) → Set
-- data _⦂_≈ₑ⦅_⦆_ : (s : 𝕊) → (e₁ : ∅ ⊢ₑ s) → (ζ : ℒ) → (e₂ : ∅ ⊢ₑ s) → Set

-- data _⦂_≈ᵥ⦅_⦆_ where
--   ≈ᵥ-`𝔹 : ∀ {𝓁 ζ}
--         → (v₁ v₂ : ∅ ⊢ᵥ `𝔹 / 𝓁)
--         → 𝓁 ⊑ ζ
--         → v₁ ≡ v₂
--         → (`𝔹 / 𝓁) ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂

--   ≈ᵥ-⇒ : ∀ {s₁ s₂ 𝓁 ζ}
--        → (v₁ v₂ : ∅ ⊢ᵥ (s₁ ⇒ s₂) / 𝓁)
--        → 𝓁 ⊑ ζ
--        → (∀ {v₁′ v₂′ : ∅ ⊢ᵥ s₁}
--             → s₁ ⦂ v₁′ ≈ᵥ⦅ ζ ⦆ v₂′
--             → (s₂ ⊔ₛ 𝓁) ⦂ ((val v₁) · (val v₁′)) ≈ₑ⦅ ζ ⦆ ((val v₂) · (val v₂′)))
--        → ((s₁ ⇒ s₂) / 𝓁) ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂

-- {-# NO_POSITIVITY_CHECK #-}
-- data _⦂_≈ₑ⦅_⦆_ where
--   ≈ₑ-e : ∀ {s ζ}
--        → (e₁ e₂ : ∅ ⊢ₑ s)
--        → (v₁ v₂ : ∅ ⊢ᵥ s)
--        → e₁ ⇓ v₁
--        → e₂ ⇓ v₂
--        → s ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
--        → s ⦂ e₁ ≈ₑ⦅ ζ ⦆ e₂


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
  → (e : Γ ⊢ₑ (t / 𝓁))
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    -----------------------------------------------
  → t / 𝓁 ⦂ (substₑ σ₁ e) ≈ₑ⦅ ζ ⦆ (substₑ σ₂ e)

fundamental-lemma : ∀ {Γ ζ t₁ t₂ 𝓁₁ 𝓁₂ 𝓁 N}
  → (σ₁ σ₂ : (∀ {A} → Γ ∋ A → ∅ ⊢ₑ A))
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
  → ((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)) / 𝓁 ⦂ (ƛ (substₑ (exts σ₁) N) / 𝓁) ≈ᵥ⦅ ζ ⦆ (ƛ (substₑ (exts σ₂) N) / 𝓁)

fundamental-lemma {N = N} σ₁ σ₂ σ₁≈σ₂ = λ 𝓁⊑ζ {v₁′} {v₂′} v₁′≈v₂′ →
  λ {(⇓-app {V = v₁″} ⇓-val ⇓-val ⇓v₁″) (⇓-app {V = v₂″} ⇓-val ⇓-val ⇓v₂″) → let p = fundamental (σ₁ • (val v₁′)) (σ₂ • (val v₂′)) {!!} {!!} {!!} {!!} in  {!!}}

fundamental σ₁ σ₂ (` x) σ₁≈σ₂ = σ₁≈σ₂
fundamental σ₁ σ₂ (val (ƛ N / 𝓁)) σ₁≈σ₂ = λ {⇓-val ⇓-val → {!!} }



-- record _⇔_ (A B : Set) : Set where
--   field
--     to   : A → B
--     from : B → A

-- -- properties
-- -- non-interference of λ-sec
-- -- non-interference : ∀ {t V}
-- --   → (M : ∅ , (t / 𝐻) ⊢ₑ `𝔹 / 𝐿)
-- --   → (V₁ : ∅ ⊢ᵥ (t / 𝐻))
-- --   → (V₂ : ∅ ⊢ᵥ (t / 𝐻))
-- --     -----------------------------------------------
-- --   → ((M [ (val V₁) ]) ⇓ V) ⇔ ((M [ (val V₂) ]) ⇓ V)
-- -- non-interference {t} {V} M V₁ V₂ = record { to = {!!} ; from = {!!} }
