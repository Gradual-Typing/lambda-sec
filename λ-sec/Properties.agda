open import Data.Empty
open import Data.Product
  using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)
  renaming (_,_ to ⟨_,_⟩)
open import Data.Nat.Properties
  using (m⊔n≤o⇒m≤o; m≤n⇒m⊔n≡n; m⊔n≤o⇒n≤o)
  renaming (⊔-assoc to ⊔ₙ-assoc)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Negation using (contradiction)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)

open import Statics
open import BigStep


_/_⦂_≈ᵥ⦅_⦆_ : (t : 𝕋) → (ℓ : ℒ) → (v₁ : ∅ ⊢ᵥ (t / ℓ)) → (ζ : ℒ) → (v₂ : ∅ ⊢ᵥ (t / ℓ)) → Set
_/_⦂_≈ₑ⦅_⦆_ : (t : 𝕋) → (ℓ : ℒ) → (e₁ : ∅ ⊢ₑ (t / ℓ)) → (ζ : ℒ) → (e₂ : ∅ ⊢ₑ (t / ℓ)) → Set

`𝔹 / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ = ℓ ⊑ ζ → v₁ ≡ v₂
((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)) / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ =
    ℓ ⊑ ζ
  → (∀ {v₁′ v₂′}
       → t₁ / ℓ₁ ⦂ v₁′ ≈ᵥ⦅ ζ ⦆ v₂′
       → t₂ / ℓ₂ ⊔ ℓ ⦂ ((val v₁) · (val v₁′)) ≈ₑ⦅ ζ ⦆ ((val v₂) · (val v₂′)))

t / ℓ ⦂ e₁ ≈ₑ⦅ ζ ⦆ e₂ =
  (∀ {v₁ v₂}
    → e₁ ⇓ v₁
    → e₂ ⇓ v₂
    → t / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂)


{- Related substitutions, under typing context Γ -}
_⊢_≈ₛ⦅_⦆_ : ∀ Γ → Subst Γ ∅ → ℒ → Subst Γ ∅ → Set
Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂ = ∀ {t ℓ} → (x : Γ ∋ (t / ℓ)) → t / ℓ ⦂ (σ₁ x) ≈ₑ⦅ ζ ⦆ (σ₂ x)

⇓≡ : ∀ {s v v₁ v₂} → (_⇓_ {s} (val v) v₁) → (_⇓_ {s} (val v) v₂) → v₁ ≡ v₂
⇓≡ ⇓-val ⇓-val = refl


postulate
  exts-sub-cons : ∀ {Γ Δ A A′}
    → (σ : Subst Γ Δ)
    → (M : Γ , A′ ⊢ₑ A)
    → (N : Δ ⊢ₑ A′)
    → (substₑ (exts σ) M) [ N ] ≡ substₑ (σ • N) M

≈ₛ-• : ∀ {Γ t ℓ ζ e₁ e₂}
    → (σ₁ : Subst Γ ∅)
    → (σ₂ : Subst Γ ∅)
    → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    → t / ℓ ⦂ e₁ ≈ₑ⦅ ζ ⦆ e₂
    → (Γ , t / ℓ) ⊢ (σ₁ • e₁) ≈ₛ⦅ ζ ⦆ (σ₂ • e₂)
≈ₛ-• σ₁ σ₂ σ₁≈σ₂ e₁≈e₂ {t} {ℓ} Z = e₁≈e₂
≈ₛ-• {Γ} {ζ = ζ} σ₁ σ₂ σ₁≈σ₂ e₁≈e₂ {t} {ℓ} (S x) = σ₁≈σ₂ {t} {ℓ} x

ℓ⊑ℓ′⇒ℓ⊔ℓ′≡ℓ′ : ∀ {ℓ ℓ′}
  → ℓ ⊑ ℓ′ → ℓ ⊔ ℓ′ ≡ ℓ′
ℓ⊑ℓ′⇒ℓ⊔ℓ′≡ℓ′ {Label n} {Label n′} (⊑-l n≤n′) = cong Label (m≤n⇒m⊔n≡n n≤n′)

⊔-assoc : ∀ {ℓ₁ ℓ₂ ℓ₃}
  → (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ≡ ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃)
⊔-assoc {Label n₁} {Label n₂} {Label n₃} = cong (λ □ → Label □) (⊔ₙ-assoc n₁ n₂ n₃)

⊔ᵥ-assoc : ∀ {Γ t ℓ₁} {v : Γ ⊢ᵥ t / ℓ₁} {ℓ₂ ℓ₃}
  → (v ⊔ᵥ ℓ₂) ⊔ᵥ ℓ₃ ≡ (subst (λ □ → Γ ⊢ᵥ t / □) (sym ⊔-assoc) (v ⊔ᵥ (ℓ₂ ⊔ ℓ₃)))
⊔ᵥ-assoc {t = `𝔹} {ℓ₁} {`true/ ℓ₁} {ℓ₂} {ℓ₃} = cong-true ⊔-assoc
  where
  cong-true : ∀ {Γ ℓ ℓ′}
    → (ℓ≡ℓ′ : ℓ ≡ ℓ′)
    → `true/ ℓ ≡ subst (λ □ → Γ ⊢ᵥ `𝔹 / □) (sym ℓ≡ℓ′) (`true/ ℓ′)
  cong-true refl = refl
⊔ᵥ-assoc {t = `𝔹} {ℓ₁} {`false/ ℓ₁} {ℓ₂} {ℓ₃} = cong-false ⊔-assoc
  where
  cong-false : ∀ {Γ ℓ ℓ′}
    → (ℓ≡ℓ′ : ℓ ≡ ℓ′)
    → `false/ ℓ ≡ subst (λ □ → Γ ⊢ᵥ `𝔹 / □) (sym ℓ≡ℓ′) (`false/ ℓ′)
  cong-false refl = refl
⊔ᵥ-assoc {t = s₁ ⇒ s₂} {ℓ₁} {ƛ N / ℓ₁} {ℓ₂} {ℓ₃} = cong-ƛ ⊔-assoc
  where
  cong-ƛ : ∀ {Γ s₁ s₂ ℓ ℓ′} {N : Γ , s₁ ⊢ₑ s₂}
    → (ℓ≡ℓ′ : ℓ ≡ ℓ′)
    → ƛ N / ℓ ≡ subst (λ □ → Γ ⊢ᵥ (s₁ ⇒ s₂) / □) (sym ℓ≡ℓ′) (ƛ N / ℓ′)
  cong-ƛ refl = refl

cong-label : ∀ {t} {ℓ ℓ′ ζ : ℒ} {v₁ v₂ : ∅ ⊢ᵥ (t / ℓ)} {v₁′ v₂′ : ∅ ⊢ᵥ (t / ℓ′)}
  → (ℓ≡ℓ′ : ℓ ≡ ℓ′)
  → v₁ ≡ (subst (λ □ → ∅ ⊢ᵥ (t / □)) (sym ℓ≡ℓ′) v₁′)
  → v₂ ≡ (subst (λ □ → ∅ ⊢ᵥ (t / □)) (sym ℓ≡ℓ′) v₂′)
  → t / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂ ≡ t / ℓ′ ⦂ v₁′ ≈ᵥ⦅ ζ ⦆ v₂′
cong-label refl refl refl = refl

⊔-⊑-inv : ∀ {ℓ₁ ℓ₂ ℓ}
  → (ℓ₁ ⊔ ℓ₂) ⊑ ℓ → (ℓ₁ ⊑ ℓ) × (ℓ₂ ⊑ ℓ)
⊔-⊑-inv {Label n₁} {Label n₂} {Label n} (⊑-l n₁⊔n₂≤n) = ⟨ left , right ⟩
  where
  left : _
  left = ⊑-l {n₁} {n} (m⊔n≤o⇒m≤o n₁ n₂ n₁⊔n₂≤n)
  right : _
  right = ⊑-l {n₂} {n} (m⊔n≤o⇒n≤o n₁ n₂ n₁⊔n₂≤n)

-- Value stamping ⊔ᵥ preserves the logical relation ≈ᵥ .
value-stamp-pres : ∀ {t ℓ ζ v₁ v₂}
  → (ℓ′ : ℒ)
  → t / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
    -----------------------------------------------
  → t / (ℓ ⊔ ℓ′) ⦂ (v₁ ⊔ᵥ ℓ′) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ ℓ′)
value-stamp-pres {ℓ = ℓ} {v₁ = `true/ ℓ} {v₂ = `true/ ℓ} ℓ′ v₁≈v₂ =
  λ _ → refl
value-stamp-pres {ℓ = ℓ} {v₁ = `true/ ℓ} {v₂ = `false/ ℓ} ℓ′ v₁≈v₂ ℓ⊔ℓ′⊑ζ =
  let ℓ⊑ζ = proj₁ (⊔-⊑-inv ℓ⊔ℓ′⊑ζ) in
  let true≡false = v₁≈v₂ ℓ⊑ζ in
    contradiction true≡false (λ ())
value-stamp-pres {ℓ = ℓ} {v₁ = `false/ ℓ} {v₂ = `true/ ℓ} ℓ′ v₁≈v₂ ℓ⊔ℓ′⊑ζ =
  let ℓ⊑ζ = proj₁ (⊔-⊑-inv ℓ⊔ℓ′⊑ζ) in
  let false≡true = v₁≈v₂ ℓ⊑ζ in
    contradiction false≡true (λ ())
value-stamp-pres {ℓ = ℓ} {v₁ = `false/ ℓ} {v₂ = `false/ ℓ} ℓ′ v₁≈v₂ =
  λ _ → refl
value-stamp-pres {(t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)} {ℓ} {ζ} {ƛ M / ℓ} {ƛ N / ℓ} ℓ′ v₁≈v₂
  with ℓ′ ⊑? ζ | ℓ ⊑? ζ
... | yes ℓ′⊑ζ | yes ℓ⊑ζ =
  λ { ℓ⊔ℓ′⊑ζ {v₁′} {v₂′} v₁′≈v₂′
      (⇓-app {V = v₁} ⇓-val ⇓-val ⇓v₁)
      (⇓-app {V = v₂} ⇓-val ⇓-val ⇓v₂) →
    let h = v₁≈v₂ ℓ⊑ζ v₁′≈v₂′ in
    let ⇓v₃ = ⇓-app {M = val (ƛ M / ℓ)} {N = val v₁′} ⇓-val ⇓-val ⇓v₁ in
    let ⇓v₄ = ⇓-app {M = val (ƛ N / ℓ)} {N = val v₂′} ⇓-val ⇓-val ⇓v₂ in
    let h′ = h ⇓v₃ ⇓v₄ in
    let h″ = value-stamp-pres ℓ′ h′ in
      subst (λ □ → □) eq h″
  }
  where
  eq : ∀ {t ℓ₁ ℓ₂ ℓ₃ ζ} {v₁ v₂ : ∅ ⊢ᵥ t / ℓ₁}
      → t / (ℓ₁ ⊔ ℓ₂) ⊔ ℓ₃ ⦂ ((v₁ ⊔ᵥ ℓ₂) ⊔ᵥ ℓ₃) ≈ᵥ⦅ ζ ⦆ ((v₂ ⊔ᵥ ℓ₂) ⊔ᵥ ℓ₃) ≡
        t / ℓ₁ ⊔ (ℓ₂ ⊔ ℓ₃) ⦂ (v₁ ⊔ᵥ (ℓ₂  ⊔ ℓ₃)) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ (ℓ₂  ⊔ ℓ₃))
  eq {t} {ℓ₁} {ℓ₂} {ℓ₃} {ζ} {v₁} {v₂} =
    cong-label (⊔-assoc {ℓ₁} {ℓ₂} {ℓ₃}) ⊔ᵥ-assoc ⊔ᵥ-assoc
... | no ¬ℓ′⊑ζ | yes ℓ⊑ζ =
  λ ℓ⊔ℓ′⊑ζ →
    let ⟨ _ , ℓ′⊑ζ ⟩ = ⊔-⊑-inv ℓ⊔ℓ′⊑ζ in
      contradiction ℓ′⊑ζ ¬ℓ′⊑ζ
... | yes ℓ′⊑ζ | no ¬ℓ⊑ζ =
  λ ℓ⊔ℓ′⊑ζ →
    let ⟨ ℓ⊑ζ , _ ⟩ = ⊔-⊑-inv ℓ⊔ℓ′⊑ζ in
      contradiction ℓ⊑ζ ¬ℓ⊑ζ
... | no ¬ℓ′⊑ζ | no ¬ℓ⊑ζ =
  λ ℓ⊔ℓ′⊑ζ →
    let ⟨ ℓ⊑ζ , _ ⟩ = ⊔-⊑-inv ℓ⊔ℓ′⊑ζ in
      contradiction ℓ⊑ζ ¬ℓ⊑ζ

≈ᵥ→≈ₑ : ∀ {t ℓ ζ v₁ v₂}
  → t / ℓ ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
  → t / ℓ ⦂ (val v₁) ≈ₑ⦅ ζ ⦆ (val v₂)
≈ᵥ→≈ₑ v₁≈v₂ = λ {⇓-val ⇓-val → v₁≈v₂}

{- Fundamental property:
   If Γ ⊢ e : s and Γ ⊢ σ₁ ≈ζ σ₂, σ₁(e) ≈ζ σ₂(e) : s
-}
fundamental : ∀ {Γ t ℓ ζ}
  → (σ₁ : Subst Γ ∅)
  → (σ₂ : Subst Γ ∅)
  → (e : Γ ⊢ₑ (t / ℓ))
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    -----------------------------------------------
  → t / ℓ ⦂ (substₑ σ₁ e) ≈ₑ⦅ ζ ⦆ (substₑ σ₂ e)
fundamental σ₁ σ₂ (` x) σ₁≈σ₂ = σ₁≈σ₂ x
fundamental σ₁ σ₂ (val (`true/ ℓ)) σ₁≈σ₂ ⇓-val ⇓-val _ = refl
fundamental σ₁ σ₂ (val (`false/ ℓ)) σ₁≈σ₂ ⇓-val ⇓-val _ = refl
fundamental {t = ((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂))} σ₁ σ₂ (val (ƛ N / ℓ)) σ₁≈σ₂ =
  λ {⇓-val ⇓-val → fundamental-ƛ {N = N} σ₁ σ₂ σ₁≈σ₂ }
  where
  fundamental-ƛ : ∀ {Γ ζ t₁ t₂ ℓ₁ ℓ₂ ℓ N}
    → (σ₁ σ₂ : Subst Γ ∅)
    → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    → ((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)) / ℓ ⦂ (ƛ (substₑ (exts σ₁) N) / ℓ) ≈ᵥ⦅ ζ ⦆ (ƛ (substₑ (exts σ₂) N) / ℓ)
  fundamental-ƛ {Γ} {ζ} {t₁} {t₂} {ℓ₁} {ℓ₂} {ℓ} {N} σ₁ σ₂ σ₁≈σ₂ = λ ℓ⊑ζ {v₁′} {v₂′} v₁′≈v₂′ →
    λ { (⇓-app {V = v₁″} ⇓-val ⇓-val ⇓v₁″) (⇓-app {V = v₂″} ⇓-val ⇓-val ⇓v₂″) →
      let σ₁•≈σ₂• = ≈ₛ-• {Γ} {t₁} {ℓ₁} {ζ} {val v₁′} {val v₂′} σ₁ σ₂ σ₁≈σ₂ (≈ᵥ→≈ₑ v₁′≈v₂′)
          σ₁•N⇓v₁″ = (subst (λ □ → □ ⇓ v₁″) (exts-sub-cons σ₁ N (val v₁′)) ⇓v₁″)
          σ₂•N⇓v₂″ = (subst (λ □ → □ ⇓ v₂″) (exts-sub-cons σ₂ N (val v₂′)) ⇓v₂″)
          ih = fundamental {ζ = ζ} (σ₁ • (val v₁′)) (σ₂ • (val v₂′)) N σ₁•≈σ₂• σ₁•N⇓v₁″ σ₂•N⇓v₂″ in
        value-stamp-pres ℓ ih }
fundamental {ζ = ζ} σ₁ σ₂ (_·_ {t₁ = t₁} {t₂} {ℓ₁} {ℓ₂} {ℓ} L N) σ₁≈σ₂
  (⇓-app {Vₙ = Vₙ₁} {V = V₁} {M′ = M₁} σ₁L⇓ƛM₁ σ₁N⇓Vₙ₁ M₁[Vₙ₁]⇓V₁) (⇓-app {Vₙ = Vₙ₂} {V = V₂} {M′ = M₂} σ₂L⇓ƛM₂ σ₂N⇓Vₙ₂ M₂[Vₙ₂]⇓V₂)
  with ℓ ⊑? ζ
... | yes ℓ⊑ζ =
  let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let ƛM₁≈ƛM₂ = σ₁L≈σ₂L σ₁L⇓ƛM₁ σ₂L⇓ƛM₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let ƛM₁·Vₙ₁≈ƛM₂·Vₙ₂ = ƛM₁≈ƛM₂ ℓ⊑ζ Vₙ₁≈Vₙ₂ in
  let ƛM₁·Vₙ₁⇓V₁ = ⇓-app {ℓ = ℓ} {Vₙ = Vₙ₁} {V = V₁} {M′ = M₁} ⇓-val ⇓-val M₁[Vₙ₁]⇓V₁ in
  let ƛM₂·Vₙ₂⇓V₂ = ⇓-app {ℓ = ℓ} {Vₙ = Vₙ₂} {V = V₂} {M′ = M₂} ⇓-val ⇓-val M₂[Vₙ₂]⇓V₂ in
    ƛM₁·Vₙ₁≈ƛM₂·Vₙ₂ ƛM₁·Vₙ₁⇓V₁ ƛM₂·Vₙ₂⇓V₂
-- ℓ ⊑ ζ means that we can see nothing ...
... | no ¬ℓ⊑ζ with t₂
...   | `𝔹 = λ ℓ₂⊔ℓ⊑ζ → ⊥-elim (¬ℓ⊑ζ (proj₂ (⊔-⊑-inv ℓ₂⊔ℓ⊑ζ)))
...   | (_ / _) ⇒ (_ / _) = λ ℓ₂⊔ℓ⊑ζ → ⊥-elim (¬ℓ⊑ζ (proj₂ (⊔-⊑-inv ℓ₂⊔ℓ⊑ζ)))
fundamental {ζ = ζ} σ₁ σ₂ (_`∧_ {ℓ₁ = ℓ₁} {ℓ₂} M N) σ₁≈σ₂
  (⇓-∧ {Vₘ = Vₘ₁} {Vₙ = Vₙ₁} σ₁M⇓Vₘ₁ σ₁N⇓Vₙ₁) (⇓-∧ {Vₘ = Vₘ₂} {Vₙ = Vₙ₂} σ₂M⇓Vₘ₂ σ₂N⇓Vₙ₂)
  with (ℓ₁ ⊔ ℓ₂) ⊑? ζ
... | yes ℓ₁⊔ℓ₂⊑ζ =
  let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let Vₘ₁≈Vₘ₂ = σ₁M≈σ₂M σ₁M⇓Vₘ₁ σ₂M⇓Vₘ₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let ℓ₁⊑ζ = proj₁ (⊔-⊑-inv ℓ₁⊔ℓ₂⊑ζ) in
  let ℓ₂⊑ζ = proj₂ (⊔-⊑-inv ℓ₁⊔ℓ₂⊑ζ) in
  let Vₘ₁≡Vₘ₂ = Vₘ₁≈Vₘ₂ ℓ₁⊑ζ in
  let Vₙ₁≡Vₙ₂ = Vₙ₁≈Vₙ₂ ℓ₂⊑ζ in
  λ _ → cong₂ (λ □₁ □₂ → (□₁ ⟦∧⟧ □₂)) Vₘ₁≡Vₘ₂ Vₙ₁≡Vₙ₂
... | no ¬ℓ₁⊔ℓ₂⊑ζ = λ ℓ₁⊔ℓ₂⊑ζ → ⊥-elim (¬ℓ₁⊔ℓ₂⊑ζ ℓ₁⊔ℓ₂⊑ζ)
fundamental {ζ = ζ} σ₁ σ₂ (_`∨_ {ℓ₁ = ℓ₁} {ℓ₂} M N) σ₁≈σ₂
  (⇓-∨ {Vₘ = Vₘ₁} {Vₙ = Vₙ₁} σ₁M⇓Vₘ₁ σ₁N⇓Vₙ₁) (⇓-∨ {Vₘ = Vₘ₂} {Vₙ = Vₙ₂} σ₂M⇓Vₘ₂ σ₂N⇓Vₙ₂)
  with (ℓ₁ ⊔ ℓ₂) ⊑? ζ
... | yes ℓ₁⊔ℓ₂⊑ζ =
  let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let Vₘ₁≈Vₘ₂ = σ₁M≈σ₂M σ₁M⇓Vₘ₁ σ₂M⇓Vₘ₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let ℓ₁⊑ζ = proj₁ (⊔-⊑-inv ℓ₁⊔ℓ₂⊑ζ) in
  let ℓ₂⊑ζ = proj₂ (⊔-⊑-inv ℓ₁⊔ℓ₂⊑ζ) in
  let Vₘ₁≡Vₘ₂ = Vₘ₁≈Vₘ₂ ℓ₁⊑ζ in
  let Vₙ₁≡Vₙ₂ = Vₙ₁≈Vₙ₂ ℓ₂⊑ζ in
  λ _ → cong₂ (λ □₁ □₂ → (□₁ ⟦∨⟧ □₂)) Vₘ₁≡Vₘ₂ Vₙ₁≡Vₙ₂
... | no ¬ℓ₁⊔ℓ₂⊑ζ = λ ℓ₁⊔ℓ₂⊑ζ → ⊥-elim (¬ℓ₁⊔ℓ₂⊑ζ ℓ₁⊔ℓ₂⊑ζ)
fundamental {ζ = ζ} σ₁ σ₂ (if {t = t} {ℓ} {ℓ′} L M N) σ₁≈σ₂
  with (ℓ ⊔ ℓ′) ⊑? ζ
... | yes ℓ⊔ℓ′⊑ζ = λ { (⇓-cond₁ _ σ₁M⇓V₁) (⇓-cond₁ _ σ₂M⇓V₂) →
        let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
          σ₁M≈σ₂M σ₁M⇓V₁ σ₂M⇓V₂ ;
      (⇓-cond₁ σ₁L⇓true _) (⇓-cond₂ σ₂L⇓false _) →
        let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
        let true≈false = σ₁L≈σ₂L σ₁L⇓true σ₂L⇓false in
        let ℓ′⊑ζ = proj₂ (⊔-⊑-inv ℓ⊔ℓ′⊑ζ) in
        let true≡false = true≈false ℓ′⊑ζ in
          contradiction true≡false (λ ()) ;
      (⇓-cond₂ σ₁L⇓false _) (⇓-cond₁ σ₂L⇓true _) →
        let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
        let false≈true = σ₁L≈σ₂L σ₁L⇓false σ₂L⇓true in
        let ℓ′⊑ζ = proj₂ (⊔-⊑-inv ℓ⊔ℓ′⊑ζ) in
        let false≡true = false≈true ℓ′⊑ζ in
          contradiction false≡true (λ ()) ;
      (⇓-cond₂ _ σ₁N⇓V₁) (⇓-cond₂ _ σ₂N⇓V₂) →
        let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
          σ₁N≈σ₂N σ₁N⇓V₁ σ₂N⇓V₂}
... | no ¬ℓ⊔ℓ′⊑ζ with t
...   | `𝔹 = λ _ _ ℓ⊔ℓ′⊑ζ → ⊥-elim (¬ℓ⊔ℓ′⊑ζ ℓ⊔ℓ′⊑ζ)
...   | (_ / _) ⇒ (_ / _) = λ _ _ ℓ⊔ℓ′⊑ζ → ⊥-elim (¬ℓ⊔ℓ′⊑ζ ℓ⊔ℓ′⊑ζ)


-- Noninterference is a corollary of the fundamental property.
noninterference : ∀ {tᵢₙ tₒᵤₜ ℓᵢₙ ℓₒᵤₜ ζ} {M : ∅ , tᵢₙ / ℓᵢₙ ⊢ₑ tₒᵤₜ / ℓₒᵤₜ} {V₁ V₂ : ∅ ⊢ᵥ tᵢₙ / ℓᵢₙ}
  → ¬ ℓᵢₙ  ⊑ ζ
  →   ℓₒᵤₜ ⊑ ζ
    --------------------------------------------------------
  → tₒᵤₜ / ℓₒᵤₜ ⦂ (M [ (val V₁) ]) ≈ₑ⦅ ζ ⦆ (M [ (val V₂) ])
noninterference {tᵢₙ} {tₒᵤₜ} {ℓᵢₙ} {ℓₒᵤₜ} {ζ} {M} {V₁} {V₂} ¬ℓᵢₙ⊑ζ ℓₒᵤₜ⊑ζ =
  let [V₁]≈[V₂] = σ₁≈σ₂ {tᵢₙ} {ℓᵢₙ} {ζ} {V₁} {V₂} ¬ℓᵢₙ⊑ζ in
    fundamental {ζ = ζ} (σ₀ (val V₁)) (σ₀ (val V₂)) M [V₁]≈[V₂]
  where
  σ₁≈σ₂ : ∀ {t ℓ ζ V₁ V₂} → (¬ℓ⊑ζ : ¬ ℓ ⊑ ζ) → (∅ , t / ℓ) ⊢ σ₀ (val V₁) ≈ₛ⦅ ζ ⦆ σ₀ (val V₂)
  σ₁≈σ₂ {t} ¬ℓ⊑ζ Z ⇓-val ⇓-val with t
  ... | `𝔹 = λ ℓ⊑ζ → ⊥-elim (¬ℓ⊑ζ ℓ⊑ζ)
  ... | (_ / _) ⇒ (_ / _) = λ ℓ⊑ζ → ⊥-elim (¬ℓ⊑ζ ℓ⊑ζ)

noninterference-high-and-low :
  ∀ {t} {M : ∅ , t / High ⊢ₑ `𝔹 / Low }
        {V₁ V₂ : ∅ ⊢ᵥ t / High} {V₁′ V₂′ : ∅ ⊢ᵥ `𝔹 / Low}
  → (M [ (val V₁) ]) ⇓ V₁′ -- input V₁ ⇒ output V₁′
  → (M [ (val V₂) ]) ⇓ V₂′ -- input V₂ ⇒ output V₂′
    ----------------------------------------------------
  → V₁′ ≡ V₂′               -- then they are the same 𝔹
noninterference-high-and-low {t} {M} {V₁} {V₂} {V₁′} {V₂′} =
  let noninterf = noninterference {t} {`𝔹} {High} {Low} {Low} {M} {V₁} {V₂} (λ {(⊑-l ())}) ⊑-refl in
    λ M[V₁]⇓V₁′ M[V₂]⇓V₂′ → noninterf M[V₁]⇓V₁′ M[V₂]⇓V₂′ ⊑-refl
