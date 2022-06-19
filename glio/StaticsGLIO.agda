module StaticsGLIO where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_; _⊓_ to _⊓ₙ_; _≟_ to _≟ₙ_)
open import Data.Nat.Properties using (≤-refl; _≤?_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

import Syntax

{-
  +------------------------------------+
  |          Index of Relations        |
  +===+================================+
  | ⊔ | Label join (ℓ)                 |
  | ⊓ | Label meet (ℓ)                 |
  | ≼ | Label partial order (ℓ)        |
  +---+--------------------------------+
  | ⋎ | Gradual label join (ℓ̂)         |
  | ⋏ | Gradual label meet (ℓ̂)         |
  | ∏ | Gradual label intersection (ℓ̂) |
  | ≾ | Label consistent subtyping (ℓ̂) |
  +---+--------------------------------+
  | ∨ | Type join (𝕋)                  |
  | ∧ | Type meet (𝕋)                  |
  | ∩ | Type intersection (𝕋)          |
  | ≲ | Type consistent subtyping (𝕋)  |
  +---+--------------------------------+
-}

pattern ⟨_,_,_⟩ x y z = ⟨ x , ⟨ y , z ⟩ ⟩

infixr 6 _[_]⇒[_]_
infixl 7 _·_
infixl 8 _`⊔_  -- join
infixl 8 _`⊓_  -- meet
infixl 9 _`≼_  -- label leq

data ℒ : Set where
  l : ℕ → ℒ

data ℒ̂ : Set where
  ¿ : ℒ̂
  l̂ : ℒ → ℒ̂


-- Examples: low and high.
𝐿 : ℒ
𝐿 = l 0
𝐿̂ = l̂ 𝐿

𝐻 : ℒ
𝐻 = l 1
𝐻̂ = l̂ 𝐻

data 𝕋 : Set where
  `⊤ : 𝕋                          -- Unit
  `𝔹 : 𝕋                         -- Bool
  `ℒ : 𝕋                         -- IF Label
  Ref : ℒ̂ → 𝕋 → 𝕋                -- Ref ℓ̂ T - reference
  Lab : ℒ̂ → 𝕋 → 𝕋                -- Lab ℓ̂ T - labeled type
  _[_]⇒[_]_ : 𝕋 → ℒ̂ → ℒ̂ → 𝕋 → 𝕋  -- T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂

-- Typing context
Context : Set
Context = List 𝕋

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] k = nothing
nth (x ∷ ls) zero = just x
nth (x ∷ ls) (suc k) = nth ls k

-- We're using the ABT library.
open Syntax using (Sig; Rename; ν; ∁; ■; _•_; id; ↑; ⟰)

data Op : Set where
  op-let : Op
  op-true       : Op
  op-false      : Op
  op-unit       : Op
  op-if  : Op
  op-lam : Op
  op-app : Op
  op-get : Op
  op-set : Op
  op-new : ℒ → Op
  op-new-dyn : Op
  op-eq-ref  : Op
  op-ref-label : Op
  op-lab-label : Op
  op-pc-label : Op
  op-label : ℒ → Op       -- Note that although we have first class labels, they cannot be ¿
  op-label-join : Op
  op-label-meet : Op
  op-label-leq : Op
  op-unlabel : Op
  op-to-label : ℒ → Op
  op-to-label-dyn : Op

sig : Op → List Sig
sig op-let      = ■ ∷ (ν ■) ∷ []
sig op-true            = []
sig op-false           = []
sig op-unit            = []
sig op-if       = ■ ∷ ■ ∷ ■ ∷ []
sig op-lam      = (ν ■) ∷ []
sig op-app      = ■ ∷ ■ ∷ []
sig op-get      = ■ ∷ []
sig op-set      = ■ ∷ ■ ∷ []
sig (op-new ℓ)  = ■ ∷ []
sig op-new-dyn  = ■ ∷ ■ ∷ []
sig op-eq-ref   = ■ ∷ ■ ∷ []
sig op-ref-label = ■ ∷ []
sig op-lab-label = ■ ∷ []
sig op-pc-label  = []  -- does not have any sub-term
sig (op-label ℓ) = []
sig op-label-join     = ■ ∷ ■ ∷ []
sig op-label-meet     = ■ ∷ ■ ∷ []
sig op-label-leq      = ■ ∷ ■ ∷ []
sig op-unlabel        = ■ ∷ []
sig (op-to-label ℓ)   = ■ ∷ []
sig op-to-label-dyn   = ■ ∷ ■ ∷ []

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫)
  renaming (ABT to Term) public

pattern `let M N = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern `true = op-true ⦅ nil ⦆
pattern `false = op-false ⦅ nil ⦆
pattern `tt = op-unit ⦅ nil ⦆
pattern if `x M N = op-if  ⦅ cons (ast `x) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ƛ N = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ `x `y = op-app ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern get `x = op-get ⦅ cons (ast `x) nil ⦆
pattern set `x `y = op-set ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern new ℓ `y = (op-new ℓ) ⦅ cons (ast `y) nil ⦆
pattern new-dyn `x `y = op-new-dyn ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern eq-ref `x `y = op-eq-ref ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern ref-label `x = op-ref-label ⦅ cons (ast `x) nil ⦆
pattern lab-label `x = op-lab-label ⦅ cons (ast `x) nil ⦆
pattern pc-label = op-pc-label ⦅ nil ⦆
pattern label ℓ = (op-label ℓ) ⦅ nil ⦆
pattern _`⊔_ `x `y = op-label-join ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern _`⊓_ `x `y = op-label-meet ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern _`≼_ `x `y = op-label-leq ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern unlabel `x = op-unlabel ⦅ cons (ast `x) nil ⦆
pattern to-label ℓ M = (op-to-label ℓ) ⦅ cons (ast M) nil ⦆
pattern to-label-dyn `x M = op-to-label-dyn ⦅ cons (ast `x) (cons (ast M) nil) ⦆


infixl 9 _≼_
infixl 9 _≾_

-- Partial order of labels
data _≼_ : ℒ → ℒ → Set where

  ≼-l : ∀ {n n′ : ℕ}
      → n ≤ n′
      → (l n) ≼ (l n′)

-- Consistent subtyping for labels
data _≾_ : ℒ̂ → ℒ̂ → Set where

  ≾-¿-r : ∀ {ℓ̂} → ℓ̂ ≾ ¿

  ≾-¿-l : ∀ {ℓ̂} → ¿ ≾ ℓ̂

  ≾-l : ∀ {ℓ₁ ℓ₂ : ℒ} → ℓ₁ ≼ ℓ₂ → (l̂ ℓ₁) ≾ (l̂ ℓ₂)

_≼?_ : (ℓ₁ ℓ₂ : ℒ) → Dec (ℓ₁ ≼ ℓ₂)
(l n₁) ≼? (l n₂) with n₁ ≤? n₂
... | yes n₁≤n₂ = yes (≼-l {n₁} {n₂} n₁≤n₂)
... | no  n₁≰n₂ = no λ {(≼-l n₁≤n₂) → n₁≰n₂ n₁≤n₂}

_≾?_ : (ℓ̂₁ ℓ̂₂ : ℒ̂) → Dec (ℓ̂₁ ≾ ℓ̂₂)
¿ ≾? _ = yes ≾-¿-l
_ ≾? ¿ = yes ≾-¿-r
(l̂ ℓ₁) ≾? (l̂ ℓ₂) with ℓ₁ ≼? ℓ₂
... | yes ℓ₁≼ℓ₂ = yes (≾-l ℓ₁≼ℓ₂)
... | no  ¬ℓ₁≼ℓ₂ = no λ {(≾-l ℓ₁≼ℓ₂) → ¬ℓ₁≼ℓ₂ ℓ₁≼ℓ₂}

≡-inv : ∀ {x y} → l x ≡ l y → x ≡ y
≡-inv refl = refl

_≟_ : (ℓ₁ : ℒ) → (ℓ₂ : ℒ) → Dec (ℓ₁ ≡ ℓ₂)
(l n₁) ≟ (l n₂) with n₁ ≟ₙ n₂
... | yes n₁≡n₂ = yes (cong (λ □ → l □) n₁≡n₂)
... | no n₁≢n₂ = no λ ℓ₁≡ℓ₂ → n₁≢n₂ (≡-inv ℓ₁≡ℓ₂)

-- Consistent subtyping for types
infixl 9 _≲_

data _≲_ : 𝕋 → 𝕋 → Set where

  ≲-⊤ :
    --------
    `⊤ ≲ `⊤

  ≲-𝔹 :
    ---------
    `𝔹 ≲ `𝔹

  ≲-ℒ :
    ---------
    `ℒ ≲ `ℒ

  ≲-Ref : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ≾ ℓ̂₂
    → ℓ̂₂ ≾ ℓ̂₁
    → T₁ ≲ T₂
    → T₂ ≲ T₁
      ----------------------
    → Ref ℓ̂₁ T₁ ≲ Ref ℓ̂₂ T₂

  ≲-Lab : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ≾ ℓ̂₂
    → T₁ ≲ T₂
      ----------------------
    → Lab ℓ̂₁ T₁ ≲ Lab ℓ̂₂ T₂

  ≲-⇒ : ∀ {ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ T₁ T₂ T₁′ T₂′}
    → ℓ̂₁′ ≾ ℓ̂₁
    → ℓ̂₂  ≾ ℓ̂₂′
    → T₁′ ≲ T₁
    → T₂  ≲ T₂′
      --------------------------------------------------
    → (T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂) ≲ (T₁′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂′)

_≲?_ : (T₁ T₂ : 𝕋) → Dec (T₁ ≲ T₂)
`⊤ ≲? `⊤ = yes ≲-⊤
`𝔹 ≲? `𝔹 = yes ≲-𝔹
`ℒ ≲? `ℒ = yes ≲-ℒ
Ref ℓ̂₁ T₁ ≲? Ref ℓ̂₂ T₂ with ℓ̂₁ ≾? ℓ̂₂
... | no ¬ℓ̂₁≾ℓ̂₂ = no λ { (≲-Ref ℓ̂₁≾ℓ̂₂ _ _ _) → ¬ℓ̂₁≾ℓ̂₂ ℓ̂₁≾ℓ̂₂ }
... | yes ℓ̂₁≾ℓ̂₂ with ℓ̂₂ ≾? ℓ̂₁
...   | no ¬ℓ̂₂≾ℓ̂₁ = no λ { (≲-Ref _ ℓ̂₂≾ℓ̂₁ _ _) → ¬ℓ̂₂≾ℓ̂₁ ℓ̂₂≾ℓ̂₁ }
...   | yes ℓ̂₂≾ℓ̂₁ with T₁ ≲? T₂
...     | no ¬T₁≲T₂ = no λ { (≲-Ref _ _ T₁≲T₂ _) → ¬T₁≲T₂ T₁≲T₂ }
...     | yes T₁≲T₂ with T₂ ≲? T₁
...       | no ¬T₂≲T₁ = no λ { (≲-Ref _ _ _ T₂≲T₁) → ¬T₂≲T₁ T₂≲T₁ }
...       | yes T₂≲T₁ = yes (≲-Ref ℓ̂₁≾ℓ̂₂ ℓ̂₂≾ℓ̂₁ T₁≲T₂ T₂≲T₁)
Lab ℓ̂₁ T₁ ≲? Lab ℓ̂₂ T₂ with ℓ̂₁ ≾? ℓ̂₂
... | no ¬ℓ̂₁≾ℓ̂₂ = no λ { (≲-Lab ℓ̂₁≾ℓ̂₂ _) → ¬ℓ̂₁≾ℓ̂₂ ℓ̂₁≾ℓ̂₂ }
... | yes ℓ̂₁≾ℓ̂₂ with T₁ ≲? T₂
...   | yes T₁≲T₂ = yes (≲-Lab ℓ̂₁≾ℓ̂₂ T₁≲T₂)
...   | no ¬T₁≲T₂ = no λ { (≲-Lab _ T₁≲T₂) → ¬T₁≲T₂ T₁≲T₂ }
(T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂) ≲? (T₁′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂′) with ℓ̂₁′ ≾? ℓ̂₁
... | no ¬ℓ̂₁′≾ℓ̂₁ = no λ { (≲-⇒ ℓ̂₁′≾ℓ̂₁ _ _ _) → ¬ℓ̂₁′≾ℓ̂₁ ℓ̂₁′≾ℓ̂₁ }
... | yes ℓ̂₁′≾ℓ̂₁ with ℓ̂₂ ≾? ℓ̂₂′
...   | no ¬ℓ̂₂≾ℓ̂₂′ = no λ { (≲-⇒ _ ℓ̂₂≾ℓ̂₂′ _ _) → ¬ℓ̂₂≾ℓ̂₂′ ℓ̂₂≾ℓ̂₂′ }
...   | yes ℓ̂₂≾ℓ̂₂′ with T₁′ ≲? T₁
...     | no ¬T₁′≲T₁ = no λ { (≲-⇒ _ _ T₁′≲T₁ _) → ¬T₁′≲T₁ T₁′≲T₁ }
...     | yes T₁′≲T₁ with T₂ ≲? T₂′
...       | no ¬T₂≲T₂′ = no λ { (≲-⇒ _ _ _ T₂≲T₂′) → ¬T₂≲T₂′ T₂≲T₂′ }
...       | yes T₂≲T₂′ = yes (≲-⇒ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′ T₁′≲T₁ T₂≲T₂′)
`⊤ ≲? `𝔹 = no λ ()
`⊤ ≲? `ℒ = no λ ()
`⊤ ≲? Ref _ _ = no λ ()
`⊤ ≲? Lab _ _ = no λ ()
`⊤ ≲? (_ [ _ ]⇒[ _ ] _) = no λ ()
`𝔹 ≲? `⊤ = no λ ()
`𝔹 ≲? `ℒ = no λ ()
`𝔹 ≲? Ref _ _ = no λ ()
`𝔹 ≲? Lab _ _ = no λ ()
`𝔹 ≲? (_ [ _ ]⇒[ _ ] _) = no λ ()
`ℒ ≲? `⊤ = no λ ()
`ℒ ≲? `𝔹 = no λ ()
`ℒ ≲? Ref _ _ = no λ ()
`ℒ ≲? Lab _ _ = no λ ()
`ℒ ≲? (_ [ _ ]⇒[ _ ] _) = no λ ()
Ref _ _ ≲? `⊤ = no λ ()
Ref _ _ ≲? `𝔹 = no λ ()
Ref _ _ ≲? `ℒ = no λ ()
Ref _ _ ≲? Lab _ _ = no λ ()
Ref _ _ ≲? (_ [ _ ]⇒[ _ ] _) = no λ ()
Lab _ _ ≲? `⊤ = no λ ()
Lab _ _ ≲? `𝔹 = no λ ()
Lab _ _ ≲? `ℒ = no λ ()
Lab _ _ ≲? Ref _ _ = no λ ()
Lab _ _ ≲? (_ [ _ ]⇒[ _ ] _) = no λ ()
(_ [ _ ]⇒[ _ ] _) ≲? `⊤ = no λ ()
(_ [ _ ]⇒[ _ ] _) ≲? `𝔹 = no λ ()
(_ [ _ ]⇒[ _ ] _) ≲? `ℒ = no λ ()
(_ [ _ ]⇒[ _ ] _) ≲? Lab _ _ = no λ ()
(_ [ _ ]⇒[ _ ] _) ≲? Ref _ _ = no λ ()


-- Label join
_⊔_ : ℒ → ℒ → ℒ
(l n₁) ⊔ (l n₂) = l (n₁ ⊔ₙ n₂)

-- Label meet
_⊓_ : ℒ → ℒ → ℒ
(l n₁) ⊓ (l n₂) = l (n₁ ⊓ₙ n₂)

-- Label gradual join
_⋎_ : ℒ̂ → ℒ̂ → ℒ̂
¿      ⋎ ¿      = ¿
(l̂ _)  ⋎ ¿      = ¿
¿      ⋎ (l̂ _)  = ¿
(l̂ ℓ₁) ⋎ (l̂ ℓ₂) = l̂ (ℓ₁ ⊔ ℓ₂)

-- Label gradual meet
_⋏_ : ℒ̂ → ℒ̂ → ℒ̂
¿      ⋏ ¿      = ¿
(l̂ _)  ⋏ ¿      = ¿
¿      ⋏ (l̂ _)  = ¿
(l̂ ℓ₁) ⋏ (l̂ ℓ₂) = l̂ (ℓ₁ ⊓ ℓ₂)

-- Label (gradual) intersection
_∏_ : ℒ̂ → ℒ̂ → Maybe ℒ̂
¿ ∏ ¿ = just ¿
¿ ∏ (l̂ ℓ) = just (l̂ ℓ)
(l̂ ℓ) ∏ ¿ = just (l̂ ℓ)
(l̂ ℓ₁) ∏ (l̂ ℓ₂) with ℓ₁ ≟ ℓ₂
... | yes _ = just (l̂ ℓ₁)
... | no _ = nothing

-- Type (gradual) intersection
_∩_ : 𝕋 → 𝕋 → Maybe 𝕋
`⊤ ∩ `⊤ = just `⊤
`𝔹 ∩ `𝔹 = just `𝔹
`ℒ ∩ `ℒ = just `ℒ
(Ref ℓ̂₁ T₁) ∩ (Ref ℓ̂₂ T₂) = do
  ℓ̂ ← ℓ̂₁ ∏ ℓ̂₂
  T ← T₁ ∩ T₂
  just (Ref ℓ̂ T)
(Lab ℓ̂₁ T₁) ∩ (Lab ℓ̂₂ T₂) = do
  ℓ̂ ← ℓ̂₁ ∏ ℓ̂₂
  T ← T₁ ∩ T₂
  just (Lab ℓ̂ T)
(T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂) ∩ (T₁′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂′) = do
  ℓ̂₁″ ← ℓ̂₁ ∏ ℓ̂₁′
  ℓ̂₂″ ← ℓ̂₂ ∏ ℓ̂₂′
  T₁″ ← T₁ ∩ T₁′
  T₂″ ← T₂ ∩ T₂′
  just (T₁″ [ ℓ̂₁″ ]⇒[ ℓ̂₂″ ] T₂″)
_ ∩ _ = nothing


mutual
  -- Type (gradual) join
  _∨_ : 𝕋 → 𝕋 → Maybe 𝕋
  `⊤ ∨ `⊤ = just `⊤
  `𝔹 ∨ `𝔹 = just `𝔹
  `ℒ ∨ `ℒ = just `ℒ
  (Ref ℓ̂₁ T₁) ∨ (Ref ℓ̂₂ T₂) = do
    ℓ̂ ← ℓ̂₁ ∏ ℓ̂₂
    T ← T₁ ∩ T₂
    just (Ref ℓ̂ T)
  (Lab ℓ̂₁ T₁) ∨ (Lab ℓ̂₂ T₂) = do
    T ← T₁ ∨ T₂
    just (Lab (ℓ̂₁ ⋎ ℓ̂₂) T)
  (T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂) ∨ (T₁′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂′) = do
    T₁″ ← T₁ ∧ T₁′
    T₂″ ← T₂ ∨ T₂′
    just (T₁″ [ ℓ̂₁ ⋏ ℓ̂₁′ ]⇒[ ℓ̂₂ ⋎ ℓ̂₂′ ] T₂″)
  _ ∨ _ = nothing

  -- Type (gradual) meet
  _∧_ : 𝕋 → 𝕋 → Maybe 𝕋
  `⊤ ∧ `⊤ = just `⊤
  `𝔹 ∧ `𝔹 = just `𝔹
  `ℒ ∧ `ℒ = just `ℒ
  (Ref ℓ̂₁ T₁) ∧ (Ref ℓ̂₂ T₂) = do
    ℓ̂ ← ℓ̂₁ ∏ ℓ̂₂
    T ← T₁ ∩ T₂
    just (Ref ℓ̂ T)
  (Lab ℓ̂₁ T₁) ∧ (Lab ℓ̂₂ T₂) = do
    T ← T₁ ∧ T₂
    just (Lab (ℓ̂₁ ⋏ ℓ̂₂) T)
  (T₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T₂) ∧ (T₁′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂′) = do
    T₁″ ← T₁ ∨ T₁′
    T₂″ ← T₂ ∧ T₂′
    just (T₁″ [ ℓ̂₁ ⋎ ℓ̂₁′ ]⇒[ ℓ̂₂ ⋏ ℓ̂₂′ ] T₂″)
  _ ∧ _ = nothing


-- -- Typing judgements
infix 4 _[_,_]⊢_⦂_

data _[_,_]⊢_⦂_ : Context → ℒ̂ → ℒ̂ → Term → 𝕋 → Set where

  ⊢` : ∀ {Γ x T ℓ̂}
    → nth Γ x ≡ just T
      -------------------- Var
    → Γ [ ℓ̂ , ℓ̂ ]⊢ ` x ⦂ T

  ⊢tt : ∀ {Γ ℓ̂}
      ---------------------- Unit
    → Γ [ ℓ̂ , ℓ̂ ]⊢ `tt ⦂ `⊤

  ⊢true : ∀ {Γ ℓ̂}
      ----------------------- True
    → Γ [ ℓ̂ , ℓ̂ ]⊢ `true ⦂ `𝔹

  ⊢false : ∀ {Γ ℓ̂}
      ------------------------ False
    → Γ [ ℓ̂ , ℓ̂ ]⊢ `false ⦂ `𝔹

  ⊢let : ∀ {Γ T T′ S M N ℓ̂₁ ℓ̂₂ ℓ̂₃}
    → Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T′
    → T ∷ Γ [ ℓ̂₂ , ℓ̂₃ ]⊢ N ⦂ S
    → T′ ≲ T
      --------------------------- Let
    → Γ [ ℓ̂₁ , ℓ̂₃ ]⊢ `let M N ⦂ S

  ⊢if : ∀ {Γ x T T′ T″ M N ℓ̂₁ ℓ̂₂ ℓ̂₂′}
    → nth Γ x ≡ just `𝔹
    → Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T
    → Γ [ ℓ̂₁ , ℓ̂₂′ ]⊢ N ⦂ T′
    → T ∨ T′ ≡ just T″
      --------------------------------------- If
    → Γ [ ℓ̂₁ , ℓ̂₂ ⋎ ℓ̂₂′ ]⊢ if (` x) M N ⦂ T″

  ⊢get : ∀ {Γ x T ℓ̂₁ ℓ̂}
    → nth Γ x ≡ just (Ref ℓ̂ T)
      --------------------------------- Get
    → Γ [ ℓ̂₁ , ℓ̂₁ ⋎ ℓ̂ ]⊢ get (` x) ⦂ T

  ⊢set : ∀ {Γ x y T T′ ℓ̂₁ ℓ̂}
    → nth Γ x ≡ just (Ref ℓ̂ T)
    → nth Γ y ≡ just T′
    → T′ ≲ T  -- the heap location need to be more secure
    → ℓ̂₁ ≾ ℓ̂  -- cannot observe the control flow since the heap location is more sensitive
      ----------------------------------- Set
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ set (` x) (` y) ⦂ `⊤

  ⊢new : ∀ {Γ y T ℓ̂₁ ℓ}
    → nth Γ y ≡ just T
    → ℓ̂₁ ≾ (l̂ ℓ)
      ---------------------------------------- New
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ new ℓ (` y) ⦂ Ref (l̂ ℓ) T

  ⊢new-dyn : ∀ {Γ x y T ℓ̂₁}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just T
      -------------------------------------------- NewDyn
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ new-dyn (` x) (` y) ⦂ Ref ¿ T

  ⊢eq-ref : ∀ {Γ x y T₁ T₂ ℓ̂₁ ℓ̂₂ ℓ̂}
    → nth Γ x ≡ just (Ref ℓ̂₁ T₁)
    → nth Γ y ≡ just (Ref ℓ̂₂ T₂)
    → T₁ ≲ T₂
    → T₂ ≲ T₁
      ------------------------------------- EqRef
    → Γ [ ℓ̂ , ℓ̂ ]⊢ eq-ref (` x) (` y) ⦂ `𝔹

  ⊢ƛ : ∀ {Γ T S N ℓ̂₁ ℓ̂₂ ℓ̂}
    → T ∷ Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ N ⦂ S
      ------------------------------------ Fun
    → Γ [ ℓ̂ , ℓ̂ ]⊢ ƛ N ⦂ T [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S

  ⊢· : ∀ {Γ x y T T′ S ℓ̂₁ ℓ̂₁′ ℓ̂₂}
    → nth Γ x ≡ just (T [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S)
    → nth Γ y ≡ just T′
    → T′ ≲ T
    → ℓ̂₁′ ≾ ℓ̂₁
      --------------------------------- App
    → Γ [ ℓ̂₁′ , ℓ̂₂ ]⊢ (` x) · (` y) ⦂ S

  ⊢ref-label : ∀ {Γ x T ℓ̂ ℓ̂₁}
    → nth Γ x ≡ just (Ref ℓ̂ T)
      ------------------------------------ RefLabel
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ ref-label (` x) ⦂ `ℒ

  ⊢lab-label : ∀ {Γ x T ℓ̂ ℓ̂₁}
    → nth Γ x ≡ just (Lab ℓ̂ T)
      ------------------------------------ LabLabel
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ lab-label (` x) ⦂ `ℒ

  ⊢pc-label : ∀ {Γ ℓ̂}
      --------------------------- PC
    → Γ [ ℓ̂ , ℓ̂ ]⊢ pc-label ⦂ `ℒ

  ⊢label : ∀ {Γ ℓ̂ ℓ}
      -------------------------- Label
    → Γ [ ℓ̂ , ℓ̂ ]⊢ label ℓ ⦂ `ℒ

  ⊢≼ : ∀ {Γ x y ℓ̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `≼
    → Γ [ ℓ̂ , ℓ̂ ]⊢ (` x) `≼ (` y) ⦂ `𝔹

  ⊢⊔ : ∀ {Γ x y ℓ̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `⊔
    → Γ [ ℓ̂ , ℓ̂ ]⊢ (` x) `⊔ (` y) ⦂ `ℒ

  ⊢⊓ : ∀ {Γ x y ℓ̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `⊓
    → Γ [ ℓ̂ , ℓ̂ ]⊢ (` x) `⊓ (` y) ⦂ `ℒ

  ⊢unlabel : ∀ {Γ x T ℓ̂ ℓ̂₁}
    → nth Γ x ≡ just (Lab ℓ̂ T)
      -------------------------------------- Unlabel
    → Γ [ ℓ̂₁ , ℓ̂₁ ⋎ ℓ̂ ]⊢ unlabel (` x) ⦂ T

  ⊢to-label : ∀ {Γ T M ℓ̂₁ ℓ̂₂ ℓ}
    → Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T
    → ℓ̂₂ ≾ ((l̂ ℓ) ⋎ ℓ̂₁)
      -------------------------------------- ToLab
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ to-label ℓ M ⦂ Lab (l̂ ℓ) T

  ⊢to-label-dyn : ∀ {Γ x T M ℓ̂₁ ℓ̂₂}
    → nth Γ x ≡ just `ℒ
    → Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T
      --------------------------------------------- ToLabDyn
    → Γ [ ℓ̂₁ , ℓ̂₁ ]⊢ to-label-dyn (` x) M ⦂ Lab ¿ T
