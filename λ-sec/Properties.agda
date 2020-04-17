open import Data.Nat.Properties using (m⊔n≤o⇒m≤o; m≤n⇒m⊔n≡n; m⊔n≤o⇒n≤o) renaming (⊔-assoc to ⊔ₙ-assoc)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (Σ; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst)
open Eq.≡-Reasoning using (_≡⟨⟩_; _≡⟨_⟩_; begin_; _∎)

open import Statics
open import BigStep


-- Logical relations: related terms and values.
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


-- Related substitutions under a typing context Γ
_⊢_≈ₛ⦅_⦆_ : ∀ Γ → Subst Γ ∅ → ℒ → Subst Γ ∅ → Set
Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂ = ∀ {t 𝓁} → (x : Γ ∋ (t / 𝓁)) → t / 𝓁 ⦂ (σ₁ x) ≈ₑ⦅ ζ ⦆ (σ₂ x)

⇓≡ : ∀ {s v v₁ v₂} → (_⇓_ {s} (val v) v₁) → (_⇓_ {s} (val v) v₂) → v₁ ≡ v₂
⇓≡ ⇓-val ⇓-val = refl


-- NOTE: this is proved in the abt library - Tianyu
postulate
  exts-sub-cons : ∀ {Γ Δ A A′}
    → (σ : Subst Γ Δ)
    → (M : Γ , A′ ⊢ₑ A)
    → (N : Δ ⊢ₑ A′)
    → (substₑ (exts σ) M) [ N ] ≡ substₑ (σ • N) M

-- Cons • preserves related substitution ≈ₛ .
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

-- Label join ⊔ is associative.
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

-- The terms `true/ 𝓁` and `false/ 𝓁` can never be the same for all 𝓁 .
true≢false : ∀ {Γ 𝓁} {M : Γ ⊢ᵥ `𝔹 / 𝓁} {N : Γ ⊢ᵥ `𝔹 / 𝓁}
  → (eqₘ : M ≡ `true/ 𝓁)
  → (eqₙ : N ≡ `false/ 𝓁)
  → M ≢ N
true≢false refl refl ()


-- Value stamping ⊔ᵥ preserves the logical relation ≈ᵥ .
value-stamp-pres : ∀ {t 𝓁 ζ v₁ v₂}
  → (𝓁′ : ℒ)
  → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
    -----------------------------------------------
  → t / (𝓁 ⊔ 𝓁′) ⦂ (v₁ ⊔ᵥ 𝓁′) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ 𝓁′)
value-stamp-pres {𝓁 = 𝓁} {v₁ = `true/ 𝓁} {v₂ = `true/ 𝓁} 𝓁′ v₁≈v₂ = λ _ → refl
value-stamp-pres {𝓁 = 𝓁} {v₁ = `true/ 𝓁} {v₂ = `false/ 𝓁} 𝓁′ v₁≈v₂ 𝓁⊔𝓁′⊑ζ =
  let 𝓁⊑ζ = ⊑-relax 𝓁⊔𝓁′⊑ζ in
  let eq = v₁≈v₂ 𝓁⊑ζ in
    ⊥-elim (true≢false refl refl eq)
value-stamp-pres {𝓁 = 𝓁} {v₁ = `false/ 𝓁} {v₂ = `true/ 𝓁} 𝓁′ v₁≈v₂ 𝓁⊔𝓁′⊑ζ =
  let 𝓁⊑ζ = ⊑-relax 𝓁⊔𝓁′⊑ζ in
  let eq = v₁≈v₂ 𝓁⊑ζ in
    ⊥-elim (true≢false refl refl (sym eq))
value-stamp-pres {𝓁 = 𝓁} {v₁ = `false/ 𝓁} {v₂ = `false/ 𝓁} 𝓁′ v₁≈v₂ = λ _ → refl
value-stamp-pres {(t₁ / 𝓁₁) ⇒ (t₂ / 𝓁₂)} {𝓁} {ζ} {ƛ M / 𝓁} {ƛ N / 𝓁} 𝓁′ v₁≈v₂ with ⊑-dec 𝓁′ ζ | ⊑-dec 𝓁 ζ
... | yes 𝓁′⊑ζ | yes 𝓁⊑ζ =  λ 𝓁⊔𝓁′⊑ζ {v₁′} {v₂′} v₁′≈v₂′ →
  λ {(⇓-app {V = v₁} ⇓-val ⇓-val ⇓v₁) (⇓-app {V = v₂} ⇓-val ⇓-val ⇓v₂) →
    let h = v₁≈v₂ 𝓁⊑ζ v₁′≈v₂′ in
    let ⇓v₃ = ⇓-app {M = val (ƛ M / 𝓁)} {N = val v₁′} ⇓-val ⇓-val ⇓v₁ in
    let ⇓v₄ = ⇓-app {M = val (ƛ N / 𝓁)} {N = val v₂′} ⇓-val ⇓-val ⇓v₂ in
    let h′ = h ⇓v₃ ⇓v₄ in
    let h″ = value-stamp-pres 𝓁′ h′ in
      subst (λ □ → □) eq h″
  }
  where
  eq : ∀ {t 𝓁₁ 𝓁₂ 𝓁₃ ζ} {v₁ v₂ : ∅ ⊢ᵥ t / 𝓁₁}
      → t / (𝓁₁ ⊔ 𝓁₂) ⊔ 𝓁₃ ⦂ ((v₁ ⊔ᵥ 𝓁₂) ⊔ᵥ 𝓁₃) ≈ᵥ⦅ ζ ⦆ ((v₂ ⊔ᵥ 𝓁₂) ⊔ᵥ 𝓁₃) ≡
        t / 𝓁₁ ⊔ (𝓁₂ ⊔ 𝓁₃) ⦂ (v₁ ⊔ᵥ (𝓁₂  ⊔ 𝓁₃)) ≈ᵥ⦅ ζ ⦆ (v₂ ⊔ᵥ (𝓁₂  ⊔ 𝓁₃))
  eq {t} {𝓁₁} {𝓁₂} {𝓁₃} {ζ} {v₁} {v₂} = cong-label (⊔-assoc {𝓁₁} {𝓁₂} {𝓁₃}) ⊔ᵥ-assoc ⊔ᵥ-assoc
... | no ¬𝓁′⊑ζ | yes 𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁′⊑ζ = (proj₂ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁′⊑ζ 𝓁′⊑ζ)
... | yes 𝓁′⊑ζ | no ¬𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁⊑ζ = (proj₁ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)
... | no ¬𝓁′⊑ζ | no ¬𝓁⊑ζ = λ 𝓁⊔𝓁′⊑ζ → let 𝓁⊑ζ = (proj₁ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ)) in ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)

≈ᵥ→≈ₑ : ∀ {t 𝓁 ζ v₁ v₂}
  → t / 𝓁 ⦂ v₁ ≈ᵥ⦅ ζ ⦆ v₂
  → t / 𝓁 ⦂ (val v₁) ≈ₑ⦅ ζ ⦆ (val v₂)
≈ᵥ→≈ₑ v₁≈v₂ = λ {⇓-val ⇓-val → v₁≈v₂}



-- Fundamental property:
--   If Γ ⊢ e : s and Γ ⊢ σ₁ ≈ζ σ₂ then σ₁(e) ≈ζ σ₂(e) : s
fundamental : ∀ {Γ t 𝓁 ζ}
  → (σ₁ : Subst Γ ∅)
  → (σ₂ : Subst Γ ∅)
  → (e : Γ ⊢ₑ (t / 𝓁))
  → Γ ⊢ σ₁ ≈ₛ⦅ ζ ⦆ σ₂
    -----------------------------------------------
  → t / 𝓁 ⦂ (substₑ σ₁ e) ≈ₑ⦅ ζ ⦆ (substₑ σ₂ e)
fundamental σ₁ σ₂ (` x) σ₁≈σ₂ = σ₁≈σ₂ x
fundamental {ζ = ζ} σ₁ σ₂ (val (`true/ 𝓁)) σ₁≈σ₂ ⇓-val ⇓-val _ = refl
fundamental σ₁ σ₂ (val (`false/ 𝓁)) σ₁≈σ₂ ⇓-val ⇓-val _ = refl
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
      let ih = fundamental {ζ = ζ} (σ₁ • (val v₁′)) (σ₂ • (val v₂′)) N σ₁•≈σ₂• σ₁•N⇓v₁″ σ₂•N⇓v₂″ in value-stamp-pres 𝓁 ih}
fundamental {ζ = ζ} σ₁ σ₂ (_·_ {t₁ = t₁} {t₂} {𝓁₁} {𝓁₂} {𝓁} L N) σ₁≈σ₂
  (⇓-app {Vₙ = Vₙ₁} {V = V₁} {M′ = M₁} σ₁L⇓ƛM₁ σ₁N⇓Vₙ₁ M₁[Vₙ₁]⇓V₁) (⇓-app {Vₙ = Vₙ₂} {V = V₂} {M′ = M₂} σ₂L⇓ƛM₂ σ₂N⇓Vₙ₂ M₂[Vₙ₂]⇓V₂)
  with ⊑-dec 𝓁 ζ
... | yes 𝓁⊑ζ =
  let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let ƛM₁≈ƛM₂ = σ₁L≈σ₂L σ₁L⇓ƛM₁ σ₂L⇓ƛM₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let ƛM₁·Vₙ₁≈ƛM₂·Vₙ₂ = ƛM₁≈ƛM₂ 𝓁⊑ζ Vₙ₁≈Vₙ₂ in
  let ƛM₁·Vₙ₁⇓V₁ = ⇓-app {𝓁 = 𝓁} {Vₙ = Vₙ₁} {V = V₁} {M′ = M₁} ⇓-val ⇓-val M₁[Vₙ₁]⇓V₁ in
  let ƛM₂·Vₙ₂⇓V₂ = ⇓-app {𝓁 = 𝓁} {Vₙ = Vₙ₂} {V = V₂} {M′ = M₂} ⇓-val ⇓-val M₂[Vₙ₂]⇓V₂ in
    ƛM₁·Vₙ₁≈ƛM₂·Vₙ₂ ƛM₁·Vₙ₁⇓V₁ ƛM₂·Vₙ₂⇓V₂
-- 𝓁 ⊑ ζ means that we can see nothing ...
... | no ¬𝓁⊑ζ with t₂
...   | `𝔹 = λ 𝓁₂⊔𝓁⊑ζ → ⊥-elim (¬𝓁⊑ζ (proj₂ (⊔-⊑-inv 𝓁₂⊔𝓁⊑ζ)))
...   | (_ / _) ⇒ (_ / _) = λ 𝓁₂⊔𝓁⊑ζ → ⊥-elim (¬𝓁⊑ζ (proj₂ (⊔-⊑-inv 𝓁₂⊔𝓁⊑ζ)))
fundamental {ζ = ζ} σ₁ σ₂ (_`∧_ {𝓁₁ = 𝓁₁} {𝓁₂} M N) σ₁≈σ₂
  (⇓-∧ {Vₘ = Vₘ₁} {Vₙ = Vₙ₁} σ₁M⇓Vₘ₁ σ₁N⇓Vₙ₁) (⇓-∧ {Vₘ = Vₘ₂} {Vₙ = Vₙ₂} σ₂M⇓Vₘ₂ σ₂N⇓Vₙ₂)
  with ⊑-dec (𝓁₁ ⊔ 𝓁₂) ζ
... | yes 𝓁₁⊔𝓁₂⊑ζ =
  let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let Vₘ₁≈Vₘ₂ = σ₁M≈σ₂M σ₁M⇓Vₘ₁ σ₂M⇓Vₘ₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let 𝓁₁⊑ζ = proj₁ (⊔-⊑-inv 𝓁₁⊔𝓁₂⊑ζ) in
  let 𝓁₂⊑ζ = proj₂ (⊔-⊑-inv 𝓁₁⊔𝓁₂⊑ζ) in
  let Vₘ₁≡Vₘ₂ = Vₘ₁≈Vₘ₂ 𝓁₁⊑ζ in
  let Vₙ₁≡Vₙ₂ = Vₙ₁≈Vₙ₂ 𝓁₂⊑ζ in
  λ _ → cong₂ (λ □₁ □₂ → (□₁ ⟦∧⟧ □₂)) Vₘ₁≡Vₘ₂ Vₙ₁≡Vₙ₂
... | no ¬𝓁₁⊔𝓁₂⊑ζ = λ 𝓁₁⊔𝓁₂⊑ζ → ⊥-elim (¬𝓁₁⊔𝓁₂⊑ζ 𝓁₁⊔𝓁₂⊑ζ)
fundamental {ζ = ζ} σ₁ σ₂ (_`∨_ {𝓁₁ = 𝓁₁} {𝓁₂} M N) σ₁≈σ₂
  (⇓-∨ {Vₘ = Vₘ₁} {Vₙ = Vₙ₁} σ₁M⇓Vₘ₁ σ₁N⇓Vₙ₁) (⇓-∨ {Vₘ = Vₘ₂} {Vₙ = Vₙ₂} σ₂M⇓Vₘ₂ σ₂N⇓Vₙ₂)
  with ⊑-dec (𝓁₁ ⊔ 𝓁₂) ζ
... | yes 𝓁₁⊔𝓁₂⊑ζ =
  let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
  let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
  let Vₘ₁≈Vₘ₂ = σ₁M≈σ₂M σ₁M⇓Vₘ₁ σ₂M⇓Vₘ₂ in
  let Vₙ₁≈Vₙ₂ = σ₁N≈σ₂N σ₁N⇓Vₙ₁ σ₂N⇓Vₙ₂ in
  let 𝓁₁⊑ζ = proj₁ (⊔-⊑-inv 𝓁₁⊔𝓁₂⊑ζ) in
  let 𝓁₂⊑ζ = proj₂ (⊔-⊑-inv 𝓁₁⊔𝓁₂⊑ζ) in
  let Vₘ₁≡Vₘ₂ = Vₘ₁≈Vₘ₂ 𝓁₁⊑ζ in
  let Vₙ₁≡Vₙ₂ = Vₙ₁≈Vₙ₂ 𝓁₂⊑ζ in
  λ _ → cong₂ (λ □₁ □₂ → (□₁ ⟦∨⟧ □₂)) Vₘ₁≡Vₘ₂ Vₙ₁≡Vₙ₂
... | no ¬𝓁₁⊔𝓁₂⊑ζ = λ 𝓁₁⊔𝓁₂⊑ζ → ⊥-elim (¬𝓁₁⊔𝓁₂⊑ζ 𝓁₁⊔𝓁₂⊑ζ)
fundamental {ζ = ζ} σ₁ σ₂ (if {t = t} {𝓁} {𝓁′} L M N) σ₁≈σ₂
  with ⊑-dec (𝓁 ⊔ 𝓁′) ζ
... | yes 𝓁⊔𝓁′⊑ζ = λ { (⇓-cond₁ _ σ₁M⇓V₁) (⇓-cond₁ _ σ₂M⇓V₂) →
        let σ₁M≈σ₂M = fundamental σ₁ σ₂ M σ₁≈σ₂ in
          σ₁M≈σ₂M σ₁M⇓V₁ σ₂M⇓V₂ ;
      (⇓-cond₁ σ₁L⇓true _) (⇓-cond₂ σ₂L⇓false _) →
        let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
        let true≈false = σ₁L≈σ₂L σ₁L⇓true σ₂L⇓false in
        let 𝓁′⊑ζ = proj₂ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ) in
        let true≡false = true≈false 𝓁′⊑ζ in
          ⊥-elim (true≢false refl refl true≡false) ;
      (⇓-cond₂ σ₁L⇓false _) (⇓-cond₁ σ₂L⇓true _) →
        let σ₁L≈σ₂L = fundamental σ₁ σ₂ L σ₁≈σ₂ in
        let false≈true = σ₁L≈σ₂L σ₁L⇓false σ₂L⇓true in
        let 𝓁′⊑ζ = proj₂ (⊔-⊑-inv 𝓁⊔𝓁′⊑ζ) in
        let false≡true = false≈true 𝓁′⊑ζ in
          ⊥-elim (true≢false refl refl (sym false≡true)) ;
      (⇓-cond₂ _ σ₁N⇓V₁) (⇓-cond₂ _ σ₂N⇓V₂) →
        let σ₁N≈σ₂N = fundamental σ₁ σ₂ N σ₁≈σ₂ in
          σ₁N≈σ₂N σ₁N⇓V₁ σ₂N⇓V₂}
... | no ¬𝓁⊔𝓁′⊑ζ with t
...   | `𝔹 = λ _ _ 𝓁⊔𝓁′⊑ζ → ⊥-elim (¬𝓁⊔𝓁′⊑ζ 𝓁⊔𝓁′⊑ζ)
...   | (_ / _) ⇒ (_ / _) = λ _ _ 𝓁⊔𝓁′⊑ζ → ⊥-elim (¬𝓁⊔𝓁′⊑ζ 𝓁⊔𝓁′⊑ζ)


-- Noninterference is a corollary of the fundamental property.
noninterference : ∀ {tᵢₙ tₒᵤₜ 𝓁ᵢₙ 𝓁ₒᵤₜ ζ} {M : ∅ , tᵢₙ / 𝓁ᵢₙ ⊢ₑ tₒᵤₜ / 𝓁ₒᵤₜ} {V₁ : ∅ ⊢ᵥ tᵢₙ / 𝓁ᵢₙ} {V₂ : ∅ ⊢ᵥ tᵢₙ / 𝓁ᵢₙ}
  → ¬ 𝓁ᵢₙ  ⊑ ζ
  →   𝓁ₒᵤₜ ⊑ ζ
    --------------------------------------------------------
  → tₒᵤₜ / 𝓁ₒᵤₜ ⦂ (M [ (val V₁) ]) ≈ₑ⦅ ζ ⦆ (M [ (val V₂) ])
noninterference {tᵢₙ} {tₒᵤₜ} {𝓁ᵢₙ} {𝓁ₒᵤₜ} {ζ} {M} {V₁} {V₂} ¬𝓁ᵢₙ⊑ζ 𝓁ₒᵤₜ⊑ζ =
  let [V₁]≈[V₂] = σ₁≈σ₂ {tᵢₙ} {𝓁ᵢₙ} {ζ} {V₁} {V₂} ¬𝓁ᵢₙ⊑ζ in
    fundamental {ζ = ζ} (σ₀ (val V₁)) (σ₀ (val V₂)) M [V₁]≈[V₂]
  where
  σ₁≈σ₂ : ∀ {t 𝓁 ζ V₁ V₂} → (¬𝓁⊑ζ : ¬ 𝓁 ⊑ ζ) → (∅ , t / 𝓁) ⊢ σ₀ (val V₁) ≈ₛ⦅ ζ ⦆ σ₀ (val V₂)
  σ₁≈σ₂ {t} ¬𝓁⊑ζ Z ⇓-val ⇓-val with t
  ... | `𝔹 = λ 𝓁⊑ζ → ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)
  ... | (_ / _) ⇒ (_ / _) = λ 𝓁⊑ζ → ⊥-elim (¬𝓁⊑ζ 𝓁⊑ζ)
