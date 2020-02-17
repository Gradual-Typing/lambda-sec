module Statics where


open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)


-- import directly from plfa
infix  4 _⊢_
infix  4 _∋_
infixl 5 _,_

infixr 6 _⇒_
infix  7 _/_

infix  5 ƛ_⇒_
infixl 7 _·_
infixl 8 _`∧_
infixl 8 _`∨_
infix  9 `true_
infix  9 `false_
infix  9 `_
infix  9 S_  -- construct for ∋
infix  9 #_


data ℒ : Set where
  L : ℒ
  H : ℒ

mutual
  data 𝕋 : Set where
    _⇒_ : 𝕊 → 𝕊 → 𝕋
    `𝔹  : 𝕋

  data 𝕊 : Set where
    _/_ : 𝕋 → ℒ → 𝕊


data Context : Set where
  ∅   : Context
  _,_ : Context → 𝕊 → Context


data _∋_ : Context → 𝕊 → Set where

  Z : ∀ {Γ A}
      ---------
    → Γ , A ∋ A

  S_ : ∀ {Γ A B}
    → Γ ∋ A
      ---------
    → Γ , B ∋ A


-- least upper bound / join:
_⊔_ : ℒ → ℒ → ℒ
L ⊔ L = L
L ⊔ H = H
H ⊔ L = H
H ⊔ H = H

-- label stamping
_⊔ₛ_ : 𝕊 → ℒ → 𝕊
(s / 𝓁₁) ⊔ₛ 𝓁₂ = s / (𝓁₁ ⊔ 𝓁₂)

-- partial ordering of label
data _⊑_ : ℒ → ℒ → Set where

  lrefl : ∀ {𝓁 : ℒ} → 𝓁 ⊑ 𝓁

  L⊑H : L ⊑ H

-- subtyping as a relation:
mutual
  data ⊢_≤ₜ_ : 𝕋 → 𝕋 → Set where

    -- T-REFL:
    t-refl : ∀ {t : 𝕋} → ⊢ t ≤ₜ t

    -- T-TRANS:
    t-trans : ∀ {t t′ t″}
      → ⊢ t ≤ₜ t′
      → ⊢ t′ ≤ₜ t″
        ----------
      → ⊢ t ≤ₜ t″

    -- T-FUNSUB:
    t-funsub : ∀ {s₁′ s₁ s₂ s₂′}
      → ⊢ s₁′ ≤ₛ s₁
      → ⊢ s₂  ≤ₛ s₂′
        -----------
      → ⊢ (s₁ ⇒ s₂) ≤ₜ (s₁′ ⇒ s₂′)

  data ⊢_≤ₛ_ : 𝕊 → 𝕊 → Set where

    -- S-LAB
    s-lab : ∀ {t t′ 𝓁 𝓁′}
      → ⊢ t ≤ₜ t′
      → 𝓁 ⊑ 𝓁′
        ------------------
      → ⊢ (t / 𝓁) ≤ₛ (t′ / 𝓁′)




-- intrinsically-typed terms inhibit a typing judgement
data _⊢_ : Context → 𝕊 → Set where

  -- TRUE:
  `true_ : ∀ {Γ}
    → (𝓁 : ℒ)
      -------
    → Γ ⊢ `𝔹 / 𝓁

  -- FALSE
  `false_ : ∀ {Γ}
    → (𝓁 : ℒ)
      -------
    → Γ ⊢ `𝔹 / 𝓁

  -- VAR:
  `_ : ∀ {Γ A}
    → Γ ∋ A
      -----
    → Γ ⊢ A

  -- FUN:
  ƛ_⇒_  : ∀ {Γ A B}
    → (𝓁 : ℒ)
    → Γ , A ⊢ B
      ---------
    → Γ ⊢ (A ⇒ B) / 𝓁

  -- BINOPs:
  _`∧_ : ∀ {Γ 𝓁₁ 𝓁₂}
    → Γ ⊢ `𝔹 / 𝓁₁
    → Γ ⊢ `𝔹 / 𝓁₂
      -----------
    → Γ ⊢ `𝔹 / (𝓁₁ ⊔ 𝓁₂)

  _`∨_ : ∀ {Γ 𝓁₁ 𝓁₂}
    → Γ ⊢ `𝔹 / 𝓁₁
    → Γ ⊢ `𝔹 / 𝓁₂
      -----------
    → Γ ⊢ `𝔹 / (𝓁₁ ⊔ 𝓁₂)

  -- APP:
  _·_ : ∀ {Γ A B 𝓁}
    → Γ ⊢ (A ⇒ B) / 𝓁
    → Γ ⊢ A
      ---------
    → Γ ⊢ B ⊔ₛ 𝓁

  -- COND:
  if : ∀ {Γ A 𝓁}
    → Γ ⊢ `𝔹 / 𝓁
    → Γ ⊢ A ⊔ₛ 𝓁
    → Γ ⊢ A ⊔ₛ 𝓁
      ----------
    → Γ ⊢ A ⊔ₛ 𝓁

  -- SUB:
  sub : ∀ {Γ A B}
    → Γ ⊢ A
    → ⊢ A ≤ₛ B
      --------
    → Γ ⊢ B



lookup : Context → ℕ → 𝕊
lookup (Γ , A) zero     =  A
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥


-- test
_ : ∅ , (`𝔹 / H ⇒ `𝔹 / H) / L , `𝔹 / L ∋ `𝔹 / L
_ = Z

_ : ∅ , (`𝔹 / H ⇒ `𝔹 / H) / L , `𝔹 / L ∋ (`𝔹 / H ⇒ `𝔹 / H) / L
_ = S Z

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
