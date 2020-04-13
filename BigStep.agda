module BigStep where

open import Data.Nat using (ℕ; zero; suc; _≤_) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m≤n⇒m⊔n≡n; m⊔n≤o⇒n≤o) renaming (⊔-assoc to ⊔ₙ-assoc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open Eq.≡-Reasoning using (_≡⟨⟩_; _≡⟨_⟩_; begin_; _∎)
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

-- rename-ext : ∀ {Γ A B}
--   → (M : Γ ⊢ₑ B)
--   → (N : Γ ⊢ₑ A)
--   → (renameₑ S_ M) [ N ] ≡ M
-- rename-ext {Γ} {A} {B} (` x) N = refl
-- rename-ext {Γ} {A} {B} (val x) N = {!!}
-- rename-ext (M₁ `∧ M₂) N rewrite subst-dist-∧ (σ₀ N) (renameₑ S_ M₁) (renameₑ S_ M₂) | rename-ext M₁ N | rename-ext M₂ N = refl
-- rename-ext (M₁ `∨ M₂) N = {!!}
-- rename-ext (M₁ · M₂) N rewrite subst-dist-· (σ₀ N) (renameₑ S_ M₁) (renameₑ S_ M₂) | rename-ext M₁ N | rename-ext M₂ N = refl
-- rename-ext {Γ} {A} {.(_ / (_ ⊔ _))} (if M M₁ M₂) N = {!!}
-- rename-ext {Γ} {A} {B} (sub M x) N = {!!}


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


-- fundamental property
-- first we define related substitutions under a typing context Γ
_⊢_≈ₛ⦅_⦆_ : ∀ Γ → Subst Γ ∅ → ℒ → Subst Γ ∅ → Set
Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂ = ∀ {t 𝓁} → (x : Γ ∋ (t / 𝓁)) → t / 𝓁 ⦂ (σ₁ x) ≈ₑ⦅ ζ ⦆ (σ₂ x)

⇓≡ : ∀ {s v v₁ v₂} → (_⇓_ {s} (val v) v₁) → (_⇓_ {s} (val v) v₂) → v₁ ≡ v₂
⇓≡ ⇓-val ⇓-val = refl


-- this is proved in the abt library - Tianyu
postulate
  exts-sub-cons : ∀ {Γ Δ A A′}
    → (σ : Subst Γ Δ)
    → (M : Γ , A′ ⊢ₑ A)
    → (N : Δ ⊢ₑ A′)
    → (substₑ (exts σ) M) [ N ] ≡ substₑ (σ • N) M


≈ₛ-• : ∀ {Γ t 𝓁 ζ e₁ e₂}
    → (σ₁ : Subst Γ ∅)
    → (σ₂ : Subst Γ ∅)
    → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    → t / 𝓁 ⦂ e₁ ≈ₑ⦅ ζ ⦆ e₂
    → (Γ , t / 𝓁) ⊢ (σ₁ • e₁) ≈ₛ⦅ ζ ⦆ (σ₂ • e₂)
≈ₛ-• σ₁ σ₂ σ₁≈σ₂ e₁≈e₂ {t} {𝓁} Z = e₁≈e₂
≈ₛ-• {Γ} {ζ = ζ} σ₁ σ₂ σ₁≈σ₂ e₁≈e₂ {t} {𝓁} (S x) = σ₁≈σ₂ {t} {𝓁} x

⊑-relax : ∀ {𝓁 𝓁′ ζ : ℒ}
  → (𝓁 ⊔ 𝓁′) ⊑ ζ
  → 𝓁 ⊑ ζ
⊑-relax {Label n} {Label n′} {Label z} (⊑-l n⊔n′≤z) =  ⊑-l {n} {n′} (m⊔n≤o⇒m≤o n n′ n⊔n′≤z)

𝓁⊑𝓁′⇒𝓁⊔𝓁′≡𝓁′ : ∀ {𝓁 𝓁′}
  → 𝓁 ⊑ 𝓁′ → 𝓁 ⊔ 𝓁′ ≡ 𝓁′
𝓁⊑𝓁′⇒𝓁⊔𝓁′≡𝓁′ {Label n} {Label n′} (⊑-l n≤n′) = cong Label (m≤n⇒m⊔n≡n n≤n′)

⊔-assoc : ∀ {𝓁₁ 𝓁₂ 𝓁₃}
  → (𝓁₁ ⊔ 𝓁₂) ⊔ 𝓁₃ ≡ 𝓁₁ ⊔ (𝓁₂ ⊔ 𝓁₃)
⊔-assoc {Label n₁} {Label n₂} {Label n₃} = cong (λ □ → Label □) (⊔ₙ-assoc n₁ n₂ n₃)

⊔ᵥ-assoc : ∀ {Γ t 𝓁₁} {v : Γ ⊢ᵥ t / 𝓁₁} {𝓁₂ 𝓁₃}
  → (v ⊔ᵥ 𝓁₂) ⊔ᵥ 𝓁₃ ≡ (subst (λ □ → Γ ⊢ᵥ t / □) (sym ⊔-assoc) (v ⊔ᵥ (𝓁₂ ⊔ 𝓁₃)))
⊔ᵥ-assoc {t = `𝔹} {𝓁₁} {`true/ 𝓁₁} {𝓁₂} {𝓁₃} = cong-true ⊔-assoc
  where
  cong-true : ∀ {Γ 𝓁 𝓁′}
    → (𝓁≡𝓁′ : 𝓁 ≡ 𝓁′)
    → `true/ 𝓁 ≡ subst (λ □ → Γ ⊢ᵥ `𝔹 / □) (sym 𝓁≡𝓁′) (`true/ 𝓁′)
  cong-true refl = refl
⊔ᵥ-assoc {t = `𝔹} {𝓁₁} {`false/ 𝓁₁} {𝓁₂} {𝓁₃} = cong-false ⊔-assoc
  where
  cong-false : ∀ {Γ 𝓁 𝓁′}
    → (𝓁≡𝓁′ : 𝓁 ≡ 𝓁′)
    → `false/ 𝓁 ≡ subst (λ □ → Γ ⊢ᵥ `𝔹 / □) (sym 𝓁≡𝓁′) (`false/ 𝓁′)
  cong-false refl = refl
⊔ᵥ-assoc {t = s₁ ⇒ s₂} {𝓁₁} {ƛ N / 𝓁₁} {𝓁₂} {𝓁₃} = cong-ƛ ⊔-assoc
  where
  cong-ƛ : ∀ {Γ s₁ s₂ 𝓁 𝓁′} {N : Γ , s₁ ⊢ₑ s₂}
    → (𝓁≡𝓁′ : 𝓁 ≡ 𝓁′)
    → ƛ N / 𝓁 ≡ subst (λ □ → Γ ⊢ᵥ (s₁ ⇒ s₂) / □) (sym 𝓁≡𝓁′) (ƛ N / 𝓁′)
  cong-ƛ refl = refl

cong-label : ∀ {t} {𝓁 𝓁′ ζ : ℒ} {v₁ v₂ : ∅ ⊢ᵥ (t / 𝓁)} {v₁′ v₂′ : ∅ ⊢ᵥ (t / 𝓁′)}
  → (𝓁≡𝓁′ : 𝓁 ≡ 𝓁′)
  → v₁ ≡ (subst (λ □ → ∅ ⊢ᵥ (t / □)) (sym 𝓁≡𝓁′) v₁′)
  → v₂ ≡ (subst (λ □ → ∅ ⊢ᵥ (t / □)) (sym 𝓁≡𝓁′) v₂′)
  → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ ≡ t / 𝓁′ ⦂ v₁′ ≈ᵥ⦅ ζ ⦆ v₂′
cong-label refl refl refl = refl

⊔-⊑-inv : ∀ {𝓁₁ 𝓁₂ 𝓁}
  → (𝓁₁ ⊔ 𝓁₂) ⊑ 𝓁 → (𝓁₁ ⊑ 𝓁) × (𝓁₂ ⊑ 𝓁)
⊔-⊑-inv {Label n₁} {Label n₂} {Label n} (⊑-l n₁⊔n₂≤n) = ⟨ left , right ⟩
  where
  left : _
  left = ⊑-l {n₁} {n} (m⊔n≤o⇒m≤o n₁ n₂ n₁⊔n₂≤n)
  right : _
  right = ⊑-l {n₂} {n} (m⊔n≤o⇒n≤o n₁ n₂ n₁⊔n₂≤n)

value-stamp : ∀ {t 𝓁 ζ v₁ v₂}
    → (𝓁′ : ℒ)
    → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
    → t / (𝓁 ⊔ 𝓁′) ⦂ (v₁ ⊔ᵥ 𝓁′) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ 𝓁′)
value-stamp {𝓁 = 𝓁} {v₁ = `true/ 𝓁} {v₂ = `true/ 𝓁} 𝓁′ v₁≈v₂ = λ _ → refl
value-stamp {𝓁 = 𝓁} {v₁ = `true/ 𝓁} {v₂ = `false/ 𝓁} 𝓁′ v₁≈v₂ 𝓁⊔𝓁′⊑ζ =
  let 𝓁⊑ζ = ⊑-relax 𝓁⊔𝓁′⊑ζ in
  let eq = v₁≈v₂ 𝓁⊑ζ in ⊥-elim (true≢false eq)
  where
  true≢false : `true/ 𝓁 ≢ `false/ 𝓁
  true≢false = λ ()
value-stamp {𝓁 = 𝓁} {v₁ = `false/ 𝓁} {v₂ = `true/ 𝓁} 𝓁′ v₁≈v₂ 𝓁⊔𝓁′⊑ζ =
  let 𝓁⊑ζ = ⊑-relax 𝓁⊔𝓁′⊑ζ in
  let eq = v₁≈v₂ 𝓁⊑ζ in ⊥-elim (false≢true eq)
  where
  false≢true : `false/ 𝓁 ≢ `true/ 𝓁
  false≢true = λ ()
value-stamp {𝓁 = 𝓁} {v₁ = `false/ 𝓁} {v₂ = `false/ 𝓁} 𝓁′ v₁≈v₂ = λ _ → refl
value-stamp {(t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)} {𝓁} {ζ} {ƛ M / 𝓁} {ƛ N / 𝓁} 𝓁′ v₁≈v₂ with ⊑-dec 𝓁′ ζ | ⊑-dec 𝓁 ζ
... | yes 𝓁′⊑ζ | yes 𝓁⊑ζ =  λ 𝓁⊔𝓁′⊑ζ {v₁′} {v₂′} v₁′≈v₂′ →
  λ {(⇓-app {V = v₁} ⇓-val ⇓-val ⇓v₁) (⇓-app {V = v₂} ⇓-val ⇓-val ⇓v₂) →
    let h = v₁≈v₂ 𝓁⊑ζ v₁′≈v₂′ in
    let ⇓v₃ = ⇓-app {M = val (ƛ M / 𝓁)} {N = val v₁′} ⇓-val ⇓-val ⇓v₁ in
    let ⇓v₄ = ⇓-app {M = val (ƛ N / 𝓁)} {N = val v₂′} ⇓-val ⇓-val ⇓v₂ in
    let h′ = h ⇓v₃ ⇓v₄ in
    let h″ = value-stamp 𝓁′ h′ in
      subst (λ □ → □) eq h″
  }
  where
  eq : ∀ {t 𝓁₁ 𝓁₂ 𝓁₃ ζ} {v₁ v₂ : ∅ ⊢ᵥ t / 𝓁₁}
      → t / (𝓁₁ ⊔ 𝓁₂) ⊔ 𝓁₃ ⦂ ((v₁ ⊔ᵥ 𝓁₂) ⊔ᵥ 𝓁₃) ≈ᵥ⦅ ζ ⦆ ((v₂ ⊔ᵥ 𝓁₂) ⊔ᵥ 𝓁₃) ≡
        t / 𝓁₁ ⊔ (𝓁₂ ⊔ 𝓁₃) ⦂ (v₁ ⊔ᵥ (𝓁₂  ⊔ 𝓁₃)) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ (𝓁₂  ⊔ 𝓁₃))
  eq {t} {𝓁₁} {𝓁₂} {𝓁₃} {ζ} {v₁} {v₂} =
    begin
      _
      ≡⟨ cong-label (⊔-assoc {𝓁₁} {𝓁₂} {𝓁₃}) ⊔ᵥ-assoc ⊔ᵥ-assoc ⟩
      _
      ∎
... | no ¬𝓁′⊑ζ | yes 𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁′⊑ζ = (proj₂ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁′⊑ζ 𝓁′⊑ζ)
... | yes 𝓁′⊑ζ | no ¬𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁⊑ζ = (proj₁ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)
... | no ¬𝓁′⊑ζ | no ¬𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁⊑ζ = (proj₁ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)

≈ᵥ→≈ₑ : ∀ {t 𝓁 ζ v₁ v₂}
  → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
  → t / 𝓁 ⦂ (val v₁) ≈ₑ⦅ ζ ⦆ (val v₂)
≈ᵥ→≈ₑ v₁≈v₂ = λ {⇓-val ⇓-val → v₁≈v₂}


-- If Γ ⊢ e : s and Γ ⊢ σ₁ ≈ζ σ₂ then σ₁(e) ≈ζ σ₂(e) : s
fundamental : ∀ {Γ t 𝓁 ζ}
  → (σ₁ : Subst Γ ∅)
  → (σ₂ : Subst Γ ∅)
  → (e : Γ ⊢ₑ (t / 𝓁))
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    -----------------------------------------------
  → t / 𝓁 ⦂ (substₑ σ₁ e) ≈ₑ⦅ ζ ⦆ (substₑ σ₂ e)
fundamental σ₁ σ₂ (` x) σ₁≈σ₂ = σ₁≈σ₂ x
fundamental {t = ((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂))} σ₁ σ₂ (val (ƛ N / 𝓁)) σ₁≈σ₂ = λ {⇓-val ⇓-val → fundamental-ƛ {N = N} σ₁ σ₂ σ₁≈σ₂ }
  where
  fundamental-ƛ : ∀ {Γ ζ t₁ t₂ 𝓁₁ 𝓁₂ 𝓁 N}
    → (σ₁ σ₂ : Subst Γ ∅)
    → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    → ((t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)) / 𝓁 ⦂ (ƛ (substₑ (exts σ₁) N) / 𝓁) ≈ᵥ⦅ ζ ⦆ (ƛ (substₑ (exts σ₂) N) / 𝓁)
  fundamental-ƛ {Γ} {ζ} {t₁} {t₂} {𝓁₁} {𝓁₂} {𝓁} {N} σ₁ σ₂ σ₁≈σ₂ = λ 𝓁⊑ζ {v₁′} {v₂′} v₁′≈v₂′ →
    λ {(⇓-app {V = v₁″} ⇓-val ⇓-val ⇓v₁″) (⇓-app {V = v₂″} ⇓-val ⇓-val ⇓v₂″) →
      let σ₁•≈σ₂• = ≈ₛ-• {Γ} {t₁} {𝓁₁} {ζ} {val v₁′} {val v₂′} σ₁ σ₂ σ₁≈σ₂ (≈ᵥ→≈ₑ v₁′≈v₂′) in
      let σ₁•N⇓v₁″ = (subst (λ □ → □ ⇓ v₁″) (exts-sub-cons σ₁ N (val v₁′)) ⇓v₁″) in
      let σ₂•N⇓v₂″ = (subst (λ □ → □ ⇓ v₂″) (exts-sub-cons σ₂ N (val v₂′)) ⇓v₂″) in
      let ih = fundamental {ζ = ζ} (σ₁ • (val v₁′)) (σ₂ • (val v₂′)) N σ₁•≈σ₂• σ₁•N⇓v₁″ σ₂•N⇓v₂″ in value-stamp 𝓁 ih}



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
