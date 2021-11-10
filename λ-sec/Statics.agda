module Statics where

open import Data.Nat
  using (ℕ; zero; suc; _≤_; z≤n; s≤s)
  renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-refl; _≤?_)
open import Data.Empty
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Function using (case_of_)


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


data ℒ : Set where
  Label : ℕ → ℒ

Low High : ℒ
Low = Label 0
High = Label 1

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

  Z : ∀ {Γ s}
      ---------
    → Γ , s ∋ s

  S_ : ∀ {Γ s s′}
    → Γ ∋ s
      ---------
    → Γ , s′ ∋ s


-- least upper bound / join:
_⊔_ : ℒ → ℒ → ℒ
(Label n) ⊔ (Label n′) = Label (n ⊔ₙ n′)

-- label stamping
_⊔ₛ_ : 𝕊 → ℒ → 𝕊
(s / ℓ₁) ⊔ₛ ℓ₂ = s / (ℓ₁ ⊔ ℓ₂)

-- partial ordering of labels
data _⊑_ : ℒ → ℒ → Set where

  ⊑-l : ∀ {n n′ : ℕ}
      → n ≤ n′
      → (Label n) ⊑ (Label n′)

Low⊑High : Low ⊑ High
Low⊑High = ⊑-l z≤n

⊑-refl : ∀ {ℓ} → ℓ ⊑ ℓ
⊑-refl {Label n} = ⊑-l ≤-refl

-- label comparison is decidable
_⊑?_ : (ℓ : ℒ) → (ℓ′ : ℒ) → Dec (ℓ ⊑ ℓ′)
_⊑?_ (Label n) (Label n′) =
  case (n ≤? n′) of λ where
    (yes n≤n′) → yes (⊑-l n≤n′)
    (no  n≰n′) → no  λ { (⊑-l n≤n′) → n≰n′ n≤n′ }

mutual
  data _<:ₜ_ : 𝕋 → 𝕋 → Set where
    <:-𝔹 : `𝔹 <:ₜ `𝔹

    <:-⇒ : ∀ {s₁ s₁′ s₂ s₂′}
      → s₁′ <:ₛ s₁
      → s₂  <:ₛ s₂′
        -----------
      → (s₁ ⇒ s₂) <:ₜ (s₁′ ⇒ s₂′)

  data _<:ₛ_ : 𝕊 → 𝕊 → Set where
    <:-lab : ∀ {t t′ ℓ ℓ′}
      → t <:ₜ t′
      → ℓ ⊑ ℓ′
        ------------------
      → (t / ℓ) <:ₛ (t′ / ℓ′)



data _⊢ᵥ_ : Context → 𝕊 → Set
data _⊢ₑ_ : Context → 𝕊 → Set

-- values
data _⊢ᵥ_ where

  -- TRUE:
  `true/_ : ∀ {Γ}
    → (ℓ : ℒ)
      -------
    → Γ ⊢ᵥ `𝔹 / ℓ

  -- FALSE
  `false/_ : ∀ {Γ}
    → (ℓ : ℒ)
      -------
    → Γ ⊢ᵥ `𝔹 / ℓ

  -- FUN:
  ƛ_/_  : ∀ {Γ s₁ s₂}
    → Γ , s₁ ⊢ₑ s₂
    → (ℓ : ℒ)
      ---------
    → Γ ⊢ᵥ (s₁ ⇒ s₂) / ℓ

_⊔ᵥ_ : ∀ {Γ s} → Γ ⊢ᵥ s → (ℓ : ℒ) → Γ ⊢ᵥ (s ⊔ₛ ℓ)
(`true/ ℓ₁)  ⊔ᵥ ℓ   = `true/  (ℓ₁ ⊔ ℓ)
(`false/ ℓ₁) ⊔ᵥ ℓ   = `false/ (ℓ₁ ⊔ ℓ)
(ƛ N / ℓ₁)   ⊔ᵥ ℓ   = ƛ N   / (ℓ₁ ⊔ ℓ)

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
  _`∧_ : ∀ {Γ ℓ₁ ℓ₂}
    → Γ ⊢ₑ `𝔹 / ℓ₁
    → Γ ⊢ₑ `𝔹 / ℓ₂
      -----------
    → Γ ⊢ₑ `𝔹 / (ℓ₁ ⊔ ℓ₂)

  _`∨_ : ∀ {Γ ℓ₁ ℓ₂}
    → Γ ⊢ₑ `𝔹 / ℓ₁
    → Γ ⊢ₑ `𝔹 / ℓ₂
      -----------
    → Γ ⊢ₑ `𝔹 / (ℓ₁ ⊔ ℓ₂)

  -- APP:
  _·_ : ∀ {Γ t₁ t₂ ℓ₁ ℓ₂ ℓ}
    → Γ ⊢ₑ ((t₁ / ℓ₁) ⇒ (t₂ / ℓ₂)) / ℓ
    → Γ ⊢ₑ t₁ / ℓ₁
      ---------
    → Γ ⊢ₑ t₂ / (ℓ₂ ⊔ ℓ)

  -- COND:
  if : ∀ {Γ t ℓ ℓ′}
    → Γ ⊢ₑ `𝔹 / ℓ′
    → Γ ⊢ₑ t / (ℓ ⊔ ℓ′)
    → Γ ⊢ₑ t / (ℓ ⊔ ℓ′)
      ----------
    → Γ ⊢ₑ t / (ℓ ⊔ ℓ′)

  -- SUB:
  sub : ∀ {Γ s₁ s₂}
    → Γ ⊢ₑ s₁
    → s₁ <:ₛ s₂
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
_ : ∅ , (`𝔹 / High ⇒ `𝔹 / High) / Low , `𝔹 / Low ∋ `𝔹 / Low
_ = Z

_ : ∅ , (`𝔹 / High ⇒ `𝔹 / High) / Low , `𝔹 / Low ∋ (`𝔹 / High ⇒ `𝔹 / High) / Low
_ = S Z

M₅ : ∅ , ( `𝔹 / High ⇒ `𝔹 / High ) / High , `𝔹 / Low ⊢ₑ ( (`𝔹 / High ⇒ `𝔹 / High) / High ⇒ `𝔹 / High ) / Low
M₅ = val (ƛ (# 0) · (sub (# 1) (<:-lab <:-𝔹 Low⊑High)) / Low)
