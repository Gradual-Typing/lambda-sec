module Statics where


open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)



infix  4 _⊢ᵥ_
infix  4 _⊢ₑ_
infix  4 _∋_
infixl 5 _,_

infixr 6 _⇒_
infix  7 _/_

infix  5 ƛ_/_
infixl 7 _·_
infixl 8 _`∧_
infixl 8 _`∨_
infix  9 val_
infix  9 `true/_
infix  9 `false/_
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

data _⊢ᵥ_ : Context → 𝕊 → Set
data _⊢ₑ_ : Context → 𝕊 → Set

-- values
data _⊢ᵥ_ where

  -- TRUE:
  `true/_ : ∀ {Γ}
    → (𝓁 : ℒ)
      -------
    → Γ ⊢ᵥ `𝔹 / 𝓁

  -- FALSE
  `false/_ : ∀ {Γ}
    → (𝓁 : ℒ)
      -------
    → Γ ⊢ᵥ `𝔹 / 𝓁

  -- FUN:
  ƛ_/_  : ∀ {Γ s₁ s₂}
    → Γ , s₁ ⊢ₑ s₂
    → (𝓁 : ℒ)
      ---------
    → Γ ⊢ᵥ (s₁ ⇒ s₂) / 𝓁

_⊔ᵥ_ : ∀ {Γ s} → Γ ⊢ᵥ s → (𝓁 : ℒ) → Γ ⊢ᵥ (s ⊔ₛ 𝓁)
(`true/ 𝓁₁)  ⊔ᵥ 𝓁   = `true/  (𝓁₁ ⊔ 𝓁)
(`false/ 𝓁₁) ⊔ᵥ 𝓁   = `false/ (𝓁₁ ⊔ 𝓁)
(ƛ N / 𝓁₁)   ⊔ᵥ 𝓁   = ƛ N   / (𝓁₁ ⊔ 𝓁)

-- intrinsically-typed terms inhibit a typing judgement
data _⊢ₑ_ where

  -- VAR:
  `_ : ∀ {Γ s}
    → Γ ∋ s
      -----
    → Γ ⊢ₑ s

  -- VAL:
  --   construct term from a value
  val_ : ∀ {Γ s}
    → Γ ⊢ᵥ s
      -------------
    → Γ ⊢ₑ s

  -- BINOPs:
  _`∧_ : ∀ {Γ 𝓁₁ 𝓁₂}
    → Γ ⊢ₑ `𝔹 / 𝓁₁
    → Γ ⊢ₑ `𝔹 / 𝓁₂
      -----------
    → Γ ⊢ₑ `𝔹 / (𝓁₁ ⊔ 𝓁₂)

  _`∨_ : ∀ {Γ 𝓁₁ 𝓁₂}
    → Γ ⊢ₑ `𝔹 / 𝓁₁
    → Γ ⊢ₑ `𝔹 / 𝓁₂
      -----------
    → Γ ⊢ₑ `𝔹 / (𝓁₁ ⊔ 𝓁₂)

  -- APP:
  _·_ : ∀ {Γ s₁ s₂ 𝓁}
    → Γ ⊢ₑ (s₁ ⇒ s₂) / 𝓁
    → Γ ⊢ₑ s₁
      ---------
    → Γ ⊢ₑ s₂ ⊔ₛ 𝓁

  -- COND:
  if : ∀ {Γ s 𝓁}
    → Γ ⊢ₑ `𝔹 / 𝓁
    → Γ ⊢ₑ s ⊔ₛ 𝓁
    → Γ ⊢ₑ s ⊔ₛ 𝓁
      ----------
    → Γ ⊢ₑ s ⊔ₛ 𝓁

  -- SUB:
  sub : ∀ {Γ s₁ s₂}
    → Γ ⊢ₑ s₁
    → ⊢ s₁ ≤ₛ s₂
      --------
    → Γ ⊢ₑ s₂



lookup : Context → ℕ → 𝕊
lookup (Γ , s) zero     =  s
lookup (Γ , _) (suc n)  =  lookup Γ n
lookup ∅       _        =  ⊥-elim impossible
  where postulate impossible : ⊥


count : ∀ {Γ} → (n : ℕ) → Γ ∋ lookup Γ n
count {Γ , _} zero     =  Z
count {Γ , _} (suc n)  =  S (count n)
count {∅}     _        =  ⊥-elim impossible
  where postulate impossible : ⊥

#_ : ∀ {Γ} → (n : ℕ) → Γ ⊢ₑ lookup Γ n
# n  =  ` count n


-- test
_ : ∅ , (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿 , `𝔹 / 𝐿 ∋ `𝔹 / 𝐿
_ = Z

_ : ∅ , (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿 , `𝔹 / 𝐿 ∋ (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐿
_ = S Z

M₅ : ∅ , ( `𝔹 / 𝐻 ⇒ `𝔹 / 𝐻 ) / 𝐻 , `𝔹 / 𝐿 ⊢ₑ ( (`𝔹 / 𝐻 ⇒ `𝔹 / 𝐻) / 𝐻 ⇒ `𝔹 / 𝐻 ) / 𝐿
M₅ = val (ƛ (# 0) · (sub (# 1) (s-lab t-refl 𝐿⊑𝐻)) / 𝐿)


