module Statics where


open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)



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
infix  9 S_         -- constructor for ∋
infix  9 #_


-- labels:
--   for simplicity we only have low and high for now.
data ℒ : Set where
  𝐿 : ℒ
  𝐻 : ℒ


mutual
  -- types
  data 𝕋 : Set where
    _⇒_ : 𝕊 → 𝕊 → 𝕋
    `𝔹  : 𝕋

  -- security types: types with label snapped on
  data 𝕊 : Set where
    _/_ : 𝕋 → ℒ → 𝕊


data Context : Set where
  ∅   : Context
  _,_ : Context → 𝕊 → Context


data _∋_ : Context → 𝕊 → Set where

  Z : ∀ {Γ s}
      ---------
    → Γ , s ∋ s

  S_ : ∀ {Γ s s′}
    → Γ ∋ s
      ---------
    → Γ , s′ ∋ s


-- least upper bound / join:
_⊔_ : ℒ → ℒ → ℒ
𝐿 ⊔ 𝐿 = 𝐿
𝐿 ⊔ 𝐻 = 𝐻
𝐻 ⊔ 𝐿 = 𝐻
𝐻 ⊔ 𝐻 = 𝐻

-- label stamping
_⊔ₛ_ : 𝕊 → ℒ → 𝕊
(s / 𝓁₁) ⊔ₛ 𝓁₂ = s / (𝓁₁ ⊔ 𝓁₂)

-- partial ordering of labels
data _⊑_ : ℒ → ℒ → Set where

  lrefl : ∀ {𝓁 : ℒ} → 𝓁 ⊑ 𝓁

  𝐿⊑𝐻 : 𝐿 ⊑ 𝐻

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
  `_ : ∀ {Γ s}
    → Γ ∋ s
      -----
    → Γ ⊢ s

  -- FUN:
  ƛ_⇒_  : ∀ {Γ s₁ s₂}
    → (𝓁 : ℒ)
    → Γ , s₁ ⊢ s₂
      ---------
    → Γ ⊢ (s₁ ⇒ s₂) / 𝓁

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
  _·_ : ∀ {Γ s₁ s₂ 𝓁}
    → Γ ⊢ (s₁ ⇒ s₂) / 𝓁
    → Γ ⊢ s₁
      ---------
    → Γ ⊢ s₂ ⊔ₛ 𝓁

  -- COND:
  if : ∀ {Γ s 𝓁}
    → Γ ⊢ `𝔹 / 𝓁
    → Γ ⊢ s ⊔ₛ 𝓁
    → Γ ⊢ s ⊔ₛ 𝓁
      ----------
    → Γ ⊢ s ⊔ₛ 𝓁

  -- SUB:
  sub : ∀ {Γ s₁ s₂}
    → Γ ⊢ s₁
    → ⊢ s₁ ≤ₛ s₂
      --------
    → Γ ⊢ s₂



lookup : Context → ℕ → 𝕊
lookup (Γ , s) zero     =  s
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥


-- test
_ : ∅ , (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿 , `𝔹 / 𝐿 ∋ `𝔹 / 𝐿
_ = Z

_ : ∅ , (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿 , `𝔹 / 𝐿 ∋ (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿
_ = S Z

count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ lookup Γ n
# n  =  ` count n
