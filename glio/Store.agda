module Store where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; cong; cong₂)

open import StaticsGLIO
open import Lemmas


-- Store (heap) location index
Location = ℕ × ℒ × ℒ

_≟ₗ_ : (loc loc′ : Location) → Dec (loc ≡ loc′)
⟨ n , ℓ₁ , ℓ₂ ⟩ ≟ₗ ⟨ n′ , ℓ₁′ , ℓ₂′ ⟩
  with n ≟ₙ n′ | ℓ₁ ≟ ℓ₁′ | ℓ₂ ≟ ℓ₂′
... | yes n≡n′ | yes ℓ₁≡ℓ₁′ | yes ℓ₂≡ℓ₂′ =
  let p≡ = cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) ℓ₁≡ℓ₁′ ℓ₂≡ℓ₂′ in
    yes (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) n≡n′ p≡)
... | yes n≡n′ | yes ℓ₁≡ℓ₁′ | no ℓ₂≢ℓ₂′ =
  no λ p≡ → let ℓ₂≡ℓ₂′ = proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))) in ℓ₂≢ℓ₂′ ℓ₂≡ℓ₂′
... | yes n≡n′ | no ℓ₁≢ℓ₁′ | yes ℓ₂≡ℓ₂′ =
  no λ p≡ → let ℓ₁≡ℓ₁′ = proj₁ (×-≡-inv (proj₂ (×-≡-inv p≡))) in ℓ₁≢ℓ₁′ ℓ₁≡ℓ₁′
... | no n≢n′ | yes ℓ₁≡ℓ₁′ | yes ℓ₂≡ℓ₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | no n≢n′ | no ℓ₁≢ℓ₁′ | yes ℓ₂≡ℓ₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | no n≢n′ | yes ℓ₁≡ℓ₁′ | no ℓ₂≢ℓ₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | yes n≡n′ | no ℓ₁≢ℓ₁′ | no ℓ₂≢ℓ₂′ =
  no λ p≡ → let ℓ₂≡ℓ₂′ = proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))) in ℓ₂≢ℓ₂′ ℓ₂≡ℓ₂′
... | no n≢n′ | no ℓ₁≢ℓ₁′ | no ℓ₂≢ℓ₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′

-- n≢n′→loc≢loc′ : ∀ {n n′ : ℕ} {ℓ₁ ℓ₁′ ℓ₂ ℓ₂′ : ℒ}
--   → n ≢ n′
--   → ⟨ n , ℓ₁ , ℓ₂ ⟩ ≢ ⟨ n′ , ℓ₁′ , ℓ₂′ ⟩
-- n≢n′→loc≢loc′ n≢n′ = λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′

≟ₗ-≡-normal : ∀ {loc} → ∃[ eq ] (loc ≟ₗ loc ≡ yes eq)
≟ₗ-≡-normal {⟨ n , ℓ₁ , ℓ₂ ⟩}
  with n ≟ₙ n | ℓ₁ ≟ ℓ₁ | ℓ₂ ≟ ℓ₂
... | yes eq₁ | yes eq₂ | yes eq₃ =
  ⟨ cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) eq₁ (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) eq₂ eq₃) , refl ⟩
... | yes _   | yes _   | no neq  = ⊥-elim (neq refl)
... | yes _   | no neq  | yes _   = ⊥-elim (neq refl)
... | no neq  | yes _   | yes _   = ⊥-elim (neq refl)
... | yes _   | no neq  | no _    = ⊥-elim (neq refl)
... | no neq  | yes _   | no _    = ⊥-elim (neq refl)
... | no neq  | no _    | yes _   = ⊥-elim (neq refl)
... | no neq  | no _    | no _    = ⊥-elim (neq refl)

≟ₗ-≢-normal : ∀ {loc loc′} → (neq : loc ≢ loc′) → ∃[ neq′ ] (loc ≟ₗ loc′ ≡ no neq′)
≟ₗ-≢-normal {⟨ n , ℓ₁ , ℓ₂ ⟩} {⟨ n′ , ℓ₁′ , ℓ₂′ ⟩} neq
  with n ≟ₙ n′ | ℓ₁ ≟ ℓ₁′ | ℓ₂ ≟ ℓ₂′
... | yes n≡n′ | yes ℓ₁≡ℓ₁′ | yes ℓ₂≡ℓ₂′ =
  ⊥-elim (neq (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) n≡n′ (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) ℓ₁≡ℓ₁′ ℓ₂≡ℓ₂′)))
... | yes _ | yes _ | no ℓ₂≢ℓ₂′ =
  ⟨ (λ p≡ → ℓ₂≢ℓ₂′ (proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | yes _ | no ℓ₁≢ℓ₁′ | yes _ =
  ⟨ (λ p≡ → ℓ₁≢ℓ₁′ (proj₁ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | no n≢n′ | yes _ | yes _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | yes _ | no _ | no ℓ₂≢ℓ₂′ =
  ⟨ (λ p≡ → ℓ₂≢ℓ₂′ (proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | no n≢n′ | yes _ | no _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | no n≢n′ | no _ | yes _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | no n≢n′  | no _ | no _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩

mutual
  -- A closure is a term with an env
  data Clos : Set where
    <_,_,_> : ∀ {Δ T S ℓ̂₁ ℓ̂₂} → (M : Term) → Env → T ∷ Δ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ S → Clos

  data Value : Set where
    V-tt : Value

    V-true : Value
    V-false : Value

    V-label : ℒ → Value

    V-clos : Clos → Value

    {- V-proxy casts from (S ⇒ T) to (S′ ⇒ T′) , (ℓ̂₁ ℓ̂₂) to (ℓ̂₁′ ℓ̂₂′) -}
    V-proxy : (S T S′ T′  : 𝕋) → (ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ : ℒ̂)
            → S′ ≲ S → T ≲ T′
            → ℓ̂₁′ ≾ ℓ̂₁ → ℓ̂₂ ≾ ℓ̂₂′
            → Value
            → Value

    V-ref : Location → Value

    V-lab : ℒ → Value → Value

  Env : Set
  Env = List Value


data Cell (X : Set) : Set where
  _↦_ : Location → X → Cell X

Store = List (Cell (𝕋 × Value))


lookup : ∀ {X} → (μ : List (Cell X)) → Location → Maybe X
lookup [] _ = nothing
lookup ( loc ↦ x ∷ μ′ ) loc′ with loc ≟ₗ loc′
... | yes _ = just x
... | no  _ = lookup μ′ loc′

-- Examples:
private
  μ : Store
  μ = ⟨ 1 , l 2 , l 2 ⟩ ↦ ⟨ `𝔹 , V-true ⟩ ∷
      ⟨ 0 , l 0 , l 1 ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷
      ⟨ 1 , l 2 , l 2 ⟩ ↦ ⟨ `ℒ , V-label (l 0) ⟩ ∷ []

  _ : lookup μ ⟨ 0 , l 1 , l 1 ⟩ ≡ nothing
  _ = refl

  _ : lookup μ ⟨ 1 , l 2 , l 2 ⟩ ≡ just ⟨ `𝔹 , V-true ⟩
  _ = refl
