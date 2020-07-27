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
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)

open import StaticsGLIO
import Syntax
open Syntax.OpSig Op sig renaming (ABT to Term)
open import Lemmas


-- Store (heap) location index
Location = ℕ × ℒ × ℒ

_≟ₗ_ : (loc loc′ : Location) → Dec (loc ≡ loc′)
⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≟ₗ ⟨ n′ , 𝓁₁′ , 𝓁₂′ ⟩
  with n ≟ₙ n′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
... | yes n≡n′ | yes 𝓁₁≡𝓁₁′ | yes 𝓁₂≡𝓁₂′ =
  let p≡ = cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) 𝓁₁≡𝓁₁′ 𝓁₂≡𝓁₂′ in
    yes (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) n≡n′ p≡)
... | yes n≡n′ | yes 𝓁₁≡𝓁₁′ | no 𝓁₂≢𝓁₂′ =
  no λ p≡ → let 𝓁₂≡𝓁₂′ = proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))) in 𝓁₂≢𝓁₂′ 𝓁₂≡𝓁₂′
... | yes n≡n′ | no 𝓁₁≢𝓁₁′ | yes 𝓁₂≡𝓁₂′ =
  no λ p≡ → let 𝓁₁≡𝓁₁′ = proj₁ (×-≡-inv (proj₂ (×-≡-inv p≡))) in 𝓁₁≢𝓁₁′ 𝓁₁≡𝓁₁′
... | no n≢n′ | yes 𝓁₁≡𝓁₁′ | yes 𝓁₂≡𝓁₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | no n≢n′ | no 𝓁₁≢𝓁₁′ | yes 𝓁₂≡𝓁₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | no n≢n′ | yes 𝓁₁≡𝓁₁′ | no 𝓁₂≢𝓁₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′
... | yes n≡n′ | no 𝓁₁≢𝓁₁′ | no 𝓁₂≢𝓁₂′ =
  no λ p≡ → let 𝓁₂≡𝓁₂′ = proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))) in 𝓁₂≢𝓁₂′ 𝓁₂≡𝓁₂′
... | no n≢n′ | no 𝓁₁≢𝓁₁′ | no 𝓁₂≢𝓁₂′ =
  no λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′

-- n≢n′→loc≢loc′ : ∀ {n n′ : ℕ} {𝓁₁ 𝓁₁′ 𝓁₂ 𝓁₂′ : ℒ}
--   → n ≢ n′
--   → ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ≢ ⟨ n′ , 𝓁₁′ , 𝓁₂′ ⟩
-- n≢n′→loc≢loc′ n≢n′ = λ p≡ → let n≡n′ = proj₁ (×-≡-inv p≡) in n≢n′ n≡n′

≟ₗ-≡-normal : ∀ {loc} → ∃[ eq ] (loc ≟ₗ loc ≡ yes eq)
≟ₗ-≡-normal {⟨ n , 𝓁₁ , 𝓁₂ ⟩}
  with n ≟ₙ n | 𝓁₁ ≟ 𝓁₁ | 𝓁₂ ≟ 𝓁₂
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
≟ₗ-≢-normal {⟨ n , 𝓁₁ , 𝓁₂ ⟩} {⟨ n′ , 𝓁₁′ , 𝓁₂′ ⟩} neq
  with n ≟ₙ n′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
... | yes n≡n′ | yes 𝓁₁≡𝓁₁′ | yes 𝓁₂≡𝓁₂′ =
  ⊥-elim (neq (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) n≡n′ (cong₂ (λ □₁ □₂ → ⟨ □₁ , □₂ ⟩) 𝓁₁≡𝓁₁′ 𝓁₂≡𝓁₂′)))
... | yes _ | yes _ | no 𝓁₂≢𝓁₂′ =
  ⟨ (λ p≡ → 𝓁₂≢𝓁₂′ (proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | yes _ | no 𝓁₁≢𝓁₁′ | yes _ =
  ⟨ (λ p≡ → 𝓁₁≢𝓁₁′ (proj₁ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | no n≢n′ | yes _ | yes _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | yes _ | no _ | no 𝓁₂≢𝓁₂′ =
  ⟨ (λ p≡ → 𝓁₂≢𝓁₂′ (proj₂ (×-≡-inv (proj₂ (×-≡-inv p≡))))) , refl ⟩
... | no n≢n′ | yes _ | no _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | no n≢n′ | no _ | yes _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩
... | no n≢n′  | no _ | no _ =
  ⟨ (λ p≡ → n≢n′ (proj₁ (×-≡-inv p≡))) , refl ⟩

mutual
  -- A closure is a term with an env
  data Clos : Set where
    <_,_,_> : ∀ {Δ T S 𝓁̂₁ 𝓁̂₂} → (M : Term) → Env → T ∷ Δ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ S → Clos

  data Value : Set where
    V-tt : Value

    V-true : Value
    V-false : Value

    V-label : ℒ → Value

    V-clos : Clos → Value

    {- V-proxy casts from (S ⇒ T) to (S′ ⇒ T′) , (𝓁̂₁ 𝓁̂₂) to (𝓁̂₁′ 𝓁̂₂′) -}
    V-proxy : (S T S′ T′  : 𝕋) → (𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ : ℒ̂)
            → S′ ≲ S → T ≲ T′
            → 𝓁̂₁′ ≾ 𝓁̂₁ → 𝓁̂₂ ≾ 𝓁̂₂′
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
