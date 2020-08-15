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
  | ⊔ | Label join (𝓁)                 |
  | ⊓ | Label meet (𝓁)                 |
  | ≼ | Label partial order (𝓁)        |
  +---+--------------------------------+
  | ⋎ | Gradual label join (𝓁̂)         |
  | ⋏ | Gradual label meet (𝓁̂)         |
  | ∏ | Gradual label intersection (𝓁̂) |
  | ≾ | Label consistent subtyping (𝓁̂) |
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
  Ref : ℒ̂ → 𝕋 → 𝕋                -- Ref 𝓁̂ T - reference
  Lab : ℒ̂ → 𝕋 → 𝕋                -- Lab 𝓁̂ T - labeled type
  _[_]⇒[_]_ : 𝕋 → ℒ̂ → ℒ̂ → 𝕋 → 𝕋  -- T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂

-- Typing context
Context : Set
Context = List 𝕋

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth [] k = nothing
nth (x ∷ ls) zero = just x
nth (x ∷ ls) (suc k) = nth ls k

-- We're using the ABT library.
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

sig : Op → List ℕ
sig op-let      = 0 ∷ 1 ∷ []
sig op-true            = []
sig op-false           = []
sig op-unit            = []
sig op-if       = 0 ∷ 0 ∷ 0 ∷ []
sig op-lam      = 1 ∷ []
sig op-app      = 0 ∷ 0 ∷ []
sig op-get      = 0 ∷ []
sig op-set      = 0 ∷ 0 ∷ []
sig (op-new 𝓁)  = 0 ∷ []
sig op-new-dyn  = 0 ∷ 0 ∷ []
sig op-eq-ref   = 0 ∷ 0 ∷ []
sig op-ref-label = 0 ∷ []
sig op-lab-label = 0 ∷ []
sig op-pc-label  = []
sig (op-label 𝓁) = []
sig op-label-join = 0 ∷ 0 ∷ []
sig op-label-meet = 0 ∷ 0 ∷ []
sig op-label-leq = 0 ∷ 0 ∷ []
sig op-unlabel = 0 ∷ []
sig (op-to-label 𝓁) = 0 ∷ []
sig op-to-label-dyn = 0 ∷ 0 ∷ []

open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)

pattern `let M N = op-let ⦅ cons (ast M) (cons (bind (ast N)) nil) ⦆
pattern `true = op-true ⦅ nil ⦆
pattern `false = op-false ⦅ nil ⦆
pattern `tt = op-unit ⦅ nil ⦆
pattern if `x M N = op-if  ⦅ cons (ast `x) (cons (ast M) (cons (ast N) nil)) ⦆
pattern ƛ N = op-lam ⦅ cons (bind (ast N)) nil ⦆
pattern _·_ `x `y = op-app ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern get `x = op-get ⦅ cons (ast `x) nil ⦆
pattern set `x `y = op-set ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern new 𝓁 `y = (op-new 𝓁) ⦅ cons (ast `y) nil ⦆
pattern new-dyn `x `y = op-new-dyn ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern eq-ref `x `y = op-eq-ref ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern ref-label `x = op-ref-label ⦅ cons (ast `x) nil ⦆
pattern lab-label `x = op-lab-label ⦅ cons (ast `x) nil ⦆
pattern pc-label = op-pc-label ⦅ nil ⦆
pattern label 𝓁 = (op-label 𝓁) ⦅ nil ⦆
pattern _`⊔_ `x `y = op-label-join ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern _`⊓_ `x `y = op-label-meet ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern _`≼_ `x `y = op-label-leq ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern unlabel `x = op-unlabel ⦅ cons (ast `x) nil ⦆
pattern to-label 𝓁 M = (op-to-label 𝓁) ⦅ cons (ast M) nil ⦆
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

  ≾-¿-r : ∀ {𝓁̂} → 𝓁̂ ≾ ¿

  ≾-¿-l : ∀ {𝓁̂} → ¿ ≾ 𝓁̂

  ≾-l : ∀ {𝓁₁ 𝓁₂ : ℒ} → 𝓁₁ ≼ 𝓁₂ → (l̂ 𝓁₁) ≾ (l̂ 𝓁₂)

_≼?_ : (𝓁₁ 𝓁₂ : ℒ) → Dec (𝓁₁ ≼ 𝓁₂)
(l n₁) ≼? (l n₂) with n₁ ≤? n₂
... | yes n₁≤n₂ = yes (≼-l {n₁} {n₂} n₁≤n₂)
... | no  n₁≰n₂ = no λ {(≼-l n₁≤n₂) → n₁≰n₂ n₁≤n₂}

_≾?_ : (𝓁̂₁ 𝓁̂₂ : ℒ̂) → Dec (𝓁̂₁ ≾ 𝓁̂₂)
¿ ≾? _ = yes ≾-¿-l
_ ≾? ¿ = yes ≾-¿-r
(l̂ 𝓁₁) ≾? (l̂ 𝓁₂) with 𝓁₁ ≼? 𝓁₂
... | yes 𝓁₁≼𝓁₂ = yes (≾-l 𝓁₁≼𝓁₂)
... | no  ¬𝓁₁≼𝓁₂ = no λ {(≾-l 𝓁₁≼𝓁₂) → ¬𝓁₁≼𝓁₂ 𝓁₁≼𝓁₂}

≡-inv : ∀ {x y} → l x ≡ l y → x ≡ y
≡-inv refl = refl

_≟_ : (𝓁₁ : ℒ) → (𝓁₂ : ℒ) → Dec (𝓁₁ ≡ 𝓁₂)
(l n₁) ≟ (l n₂) with n₁ ≟ₙ n₂
... | yes n₁≡n₂ = yes (cong (λ □ → l □) n₁≡n₂)
... | no n₁≢n₂ = no λ 𝓁₁≡𝓁₂ → n₁≢n₂ (≡-inv 𝓁₁≡𝓁₂)

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

  ≲-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ≾ 𝓁̂₂
    → 𝓁̂₂ ≾ 𝓁̂₁
    → T₁ ≲ T₂
    → T₂ ≲ T₁
      ----------------------
    → Ref 𝓁̂₁ T₁ ≲ Ref 𝓁̂₂ T₂

  ≲-Lab : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ≾ 𝓁̂₂
    → T₁ ≲ T₂
      ----------------------
    → Lab 𝓁̂₁ T₁ ≲ Lab 𝓁̂₂ T₂

  ≲-⇒ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ T₁ T₂ T₁′ T₂′}
    → 𝓁̂₁′ ≾ 𝓁̂₁
    → 𝓁̂₂  ≾ 𝓁̂₂′
    → T₁′ ≲ T₁
    → T₂  ≲ T₂′
      --------------------------------------------------
    → (T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) ≲ (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′)

_≲?_ : (T₁ T₂ : 𝕋) → Dec (T₁ ≲ T₂)
`⊤ ≲? `⊤ = yes ≲-⊤
`𝔹 ≲? `𝔹 = yes ≲-𝔹
`ℒ ≲? `ℒ = yes ≲-ℒ
Ref 𝓁̂₁ T₁ ≲? Ref 𝓁̂₂ T₂ with 𝓁̂₁ ≾? 𝓁̂₂
... | no ¬𝓁̂₁≾𝓁̂₂ = no λ { (≲-Ref 𝓁̂₁≾𝓁̂₂ _ _ _) → ¬𝓁̂₁≾𝓁̂₂ 𝓁̂₁≾𝓁̂₂ }
... | yes 𝓁̂₁≾𝓁̂₂ with 𝓁̂₂ ≾? 𝓁̂₁
...   | no ¬𝓁̂₂≾𝓁̂₁ = no λ { (≲-Ref _ 𝓁̂₂≾𝓁̂₁ _ _) → ¬𝓁̂₂≾𝓁̂₁ 𝓁̂₂≾𝓁̂₁ }
...   | yes 𝓁̂₂≾𝓁̂₁ with T₁ ≲? T₂
...     | no ¬T₁≲T₂ = no λ { (≲-Ref _ _ T₁≲T₂ _) → ¬T₁≲T₂ T₁≲T₂ }
...     | yes T₁≲T₂ with T₂ ≲? T₁
...       | no ¬T₂≲T₁ = no λ { (≲-Ref _ _ _ T₂≲T₁) → ¬T₂≲T₁ T₂≲T₁ }
...       | yes T₂≲T₁ = yes (≲-Ref 𝓁̂₁≾𝓁̂₂ 𝓁̂₂≾𝓁̂₁ T₁≲T₂ T₂≲T₁)
Lab 𝓁̂₁ T₁ ≲? Lab 𝓁̂₂ T₂ with 𝓁̂₁ ≾? 𝓁̂₂
... | no ¬𝓁̂₁≾𝓁̂₂ = no λ { (≲-Lab 𝓁̂₁≾𝓁̂₂ _) → ¬𝓁̂₁≾𝓁̂₂ 𝓁̂₁≾𝓁̂₂ }
... | yes 𝓁̂₁≾𝓁̂₂ with T₁ ≲? T₂
...   | yes T₁≲T₂ = yes (≲-Lab 𝓁̂₁≾𝓁̂₂ T₁≲T₂)
...   | no ¬T₁≲T₂ = no λ { (≲-Lab _ T₁≲T₂) → ¬T₁≲T₂ T₁≲T₂ }
(T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) ≲? (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′) with 𝓁̂₁′ ≾? 𝓁̂₁
... | no ¬𝓁̂₁′≾𝓁̂₁ = no λ { (≲-⇒ 𝓁̂₁′≾𝓁̂₁ _ _ _) → ¬𝓁̂₁′≾𝓁̂₁ 𝓁̂₁′≾𝓁̂₁ }
... | yes 𝓁̂₁′≾𝓁̂₁ with 𝓁̂₂ ≾? 𝓁̂₂′
...   | no ¬𝓁̂₂≾𝓁̂₂′ = no λ { (≲-⇒ _ 𝓁̂₂≾𝓁̂₂′ _ _) → ¬𝓁̂₂≾𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′ }
...   | yes 𝓁̂₂≾𝓁̂₂′ with T₁′ ≲? T₁
...     | no ¬T₁′≲T₁ = no λ { (≲-⇒ _ _ T₁′≲T₁ _) → ¬T₁′≲T₁ T₁′≲T₁ }
...     | yes T₁′≲T₁ with T₂ ≲? T₂′
...       | no ¬T₂≲T₂′ = no λ { (≲-⇒ _ _ _ T₂≲T₂′) → ¬T₂≲T₂′ T₂≲T₂′ }
...       | yes T₂≲T₂′ = yes (≲-⇒ 𝓁̂₁′≾𝓁̂₁ 𝓁̂₂≾𝓁̂₂′ T₁′≲T₁ T₂≲T₂′)
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
(l̂ 𝓁₁) ⋎ (l̂ 𝓁₂) = l̂ (𝓁₁ ⊔ 𝓁₂)

-- Label gradual meet
_⋏_ : ℒ̂ → ℒ̂ → ℒ̂
¿      ⋏ ¿      = ¿
(l̂ _)  ⋏ ¿      = ¿
¿      ⋏ (l̂ _)  = ¿
(l̂ 𝓁₁) ⋏ (l̂ 𝓁₂) = l̂ (𝓁₁ ⊓ 𝓁₂)

-- Label (gradual) intersection
_∏_ : ℒ̂ → ℒ̂ → Maybe ℒ̂
¿ ∏ ¿ = just ¿
¿ ∏ (l̂ 𝓁) = just (l̂ 𝓁)
(l̂ 𝓁) ∏ ¿ = just (l̂ 𝓁)
(l̂ 𝓁₁) ∏ (l̂ 𝓁₂) with 𝓁₁ ≟ 𝓁₂
... | yes _ = just (l̂ 𝓁₁)
... | no _ = nothing

-- Type (gradual) intersection
_∩_ : 𝕋 → 𝕋 → Maybe 𝕋
`⊤ ∩ `⊤ = just `⊤
`𝔹 ∩ `𝔹 = just `𝔹
`ℒ ∩ `ℒ = just `ℒ
(Ref 𝓁̂₁ T₁) ∩ (Ref 𝓁̂₂ T₂) = do
  𝓁̂ ← 𝓁̂₁ ∏ 𝓁̂₂
  T ← T₁ ∩ T₂
  just (Ref 𝓁̂ T)
(Lab 𝓁̂₁ T₁) ∩ (Lab 𝓁̂₂ T₂) = do
  𝓁̂ ← 𝓁̂₁ ∏ 𝓁̂₂
  T ← T₁ ∩ T₂
  just (Lab 𝓁̂ T)
(T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) ∩ (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′) = do
  𝓁̂₁″ ← 𝓁̂₁ ∏ 𝓁̂₁′
  𝓁̂₂″ ← 𝓁̂₂ ∏ 𝓁̂₂′
  T₁″ ← T₁ ∩ T₁′
  T₂″ ← T₂ ∩ T₂′
  just (T₁″ [ 𝓁̂₁″ ]⇒[ 𝓁̂₂″ ] T₂″)
_ ∩ _ = nothing


mutual
  -- Type (gradual) join
  _∨_ : 𝕋 → 𝕋 → Maybe 𝕋
  `⊤ ∨ `⊤ = just `⊤
  `𝔹 ∨ `𝔹 = just `𝔹
  `ℒ ∨ `ℒ = just `ℒ
  (Ref 𝓁̂₁ T₁) ∨ (Ref 𝓁̂₂ T₂) = do
    𝓁̂ ← 𝓁̂₁ ∏ 𝓁̂₂
    T ← T₁ ∩ T₂
    just (Ref 𝓁̂ T)
  (Lab 𝓁̂₁ T₁) ∨ (Lab 𝓁̂₂ T₂) = do
    T ← T₁ ∨ T₂
    just (Lab (𝓁̂₁ ⋎ 𝓁̂₂) T)
  (T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) ∨ (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′) = do
    T₁″ ← T₁ ∧ T₁′
    T₂″ ← T₂ ∨ T₂′
    just (T₁″ [ 𝓁̂₁ ⋏ 𝓁̂₁′ ]⇒[ 𝓁̂₂ ⋎ 𝓁̂₂′ ] T₂″)
  _ ∨ _ = nothing

  -- Type (gradual) meet
  _∧_ : 𝕋 → 𝕋 → Maybe 𝕋
  `⊤ ∧ `⊤ = just `⊤
  `𝔹 ∧ `𝔹 = just `𝔹
  `ℒ ∧ `ℒ = just `ℒ
  (Ref 𝓁̂₁ T₁) ∧ (Ref 𝓁̂₂ T₂) = do
    𝓁̂ ← 𝓁̂₁ ∏ 𝓁̂₂
    T ← T₁ ∩ T₂
    just (Ref 𝓁̂ T)
  (Lab 𝓁̂₁ T₁) ∧ (Lab 𝓁̂₂ T₂) = do
    T ← T₁ ∧ T₂
    just (Lab (𝓁̂₁ ⋏ 𝓁̂₂) T)
  (T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) ∧ (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′) = do
    T₁″ ← T₁ ∨ T₁′
    T₂″ ← T₂ ∧ T₂′
    just (T₁″ [ 𝓁̂₁ ⋎ 𝓁̂₁′ ]⇒[ 𝓁̂₂ ⋏ 𝓁̂₂′ ] T₂″)
  _ ∧ _ = nothing


-- -- Typing judgements
infix 4 _[_,_]⊢_⦂_

data _[_,_]⊢_⦂_ : Context → ℒ̂ → ℒ̂ → Term → 𝕋 → Set where

  ⊢` : ∀ {Γ x T 𝓁̂}
    → nth Γ x ≡ just T
      -------------------- Var
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ ` x ⦂ T

  ⊢tt : ∀ {Γ 𝓁̂}
      ---------------------- Unit
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ `tt ⦂ `⊤

  ⊢true : ∀ {Γ 𝓁̂}
      ----------------------- True
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ `true ⦂ `𝔹

  ⊢false : ∀ {Γ 𝓁̂}
      ------------------------ False
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ `false ⦂ `𝔹

  ⊢let : ∀ {Γ T T′ S M N 𝓁̂₁ 𝓁̂₂ 𝓁̂₃}
    → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T′
    → T ∷ Γ [ 𝓁̂₂ , 𝓁̂₃ ]⊢ N ⦂ S
    → T′ ≲ T
      --------------------------- Let
    → Γ [ 𝓁̂₁ , 𝓁̂₃ ]⊢ `let M N ⦂ S

  ⊢if : ∀ {Γ x T T′ T″ M N 𝓁̂₁ 𝓁̂₂ 𝓁̂₂′}
    → nth Γ x ≡ just `𝔹
    → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T
    → Γ [ 𝓁̂₁ , 𝓁̂₂′ ]⊢ N ⦂ T′
    → T ∨ T′ ≡ just T″
      --------------------------------------- If
    → Γ [ 𝓁̂₁ , 𝓁̂₂ ⋎ 𝓁̂₂′ ]⊢ if (` x) M N ⦂ T″

  ⊢get : ∀ {Γ x T 𝓁̂₁ 𝓁̂}
    → nth Γ x ≡ just (Ref 𝓁̂ T)
      --------------------------------- Get
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ⋎ 𝓁̂ ]⊢ get (` x) ⦂ T

  ⊢set : ∀ {Γ x y T T′ 𝓁̂₁ 𝓁̂}
    → nth Γ x ≡ just (Ref 𝓁̂ T)
    → nth Γ y ≡ just T′
    → T′ ≲ T  -- the heap location need to be more secure
    → 𝓁̂₁ ≾ 𝓁̂  -- cannot observe the control flow since the heap location is more sensitive
      ----------------------------------- Set
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ set (` x) (` y) ⦂ `⊤

  ⊢new : ∀ {Γ y T 𝓁̂₁ 𝓁}
    → nth Γ y ≡ just T
    → 𝓁̂₁ ≾ (l̂ 𝓁)
      ---------------------------------------- New
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ new 𝓁 (` y) ⦂ Ref (l̂ 𝓁) T

  ⊢new-dyn : ∀ {Γ x y T 𝓁̂₁}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just T
      -------------------------------------------- NewDyn
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ new-dyn (` x) (` y) ⦂ Ref ¿ T

  ⊢eq-ref : ∀ {Γ x y T₁ T₂ 𝓁̂₁ 𝓁̂₂ 𝓁̂}
    → nth Γ x ≡ just (Ref 𝓁̂₁ T₁)
    → nth Γ y ≡ just (Ref 𝓁̂₂ T₂)
    → T₁ ≲ T₂
    → T₂ ≲ T₁
      ------------------------------------- EqRef
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ eq-ref (` x) (` y) ⦂ `𝔹

  ⊢ƛ : ∀ {Γ T S N 𝓁̂₁ 𝓁̂₂ 𝓁̂}
    → T ∷ Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ N ⦂ S
      ------------------------------------ Fun
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ ƛ N ⦂ T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S

  ⊢· : ∀ {Γ x y T T′ S 𝓁̂₁ 𝓁̂₁′ 𝓁̂₂}
    → nth Γ x ≡ just (T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S)
    → nth Γ y ≡ just T′
    → T′ ≲ T
    → 𝓁̂₁′ ≾ 𝓁̂₁
      --------------------------------- App
    → Γ [ 𝓁̂₁′ , 𝓁̂₂ ]⊢ (` x) · (` y) ⦂ S

  ⊢ref-label : ∀ {Γ x T 𝓁̂ 𝓁̂₁}
    → nth Γ x ≡ just (Ref 𝓁̂ T)
      ------------------------------------ RefLabel
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ ref-label (` x) ⦂ `ℒ

  ⊢lab-label : ∀ {Γ x T 𝓁̂ 𝓁̂₁}
    → nth Γ x ≡ just (Lab 𝓁̂ T)
      ------------------------------------ LabLabel
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ lab-label (` x) ⦂ `ℒ

  ⊢pc-label : ∀ {Γ 𝓁̂}
      --------------------------- PC
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ pc-label ⦂ `ℒ

  ⊢label : ∀ {Γ 𝓁̂ 𝓁}
      -------------------------- Label
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ label 𝓁 ⦂ `ℒ

  ⊢≼ : ∀ {Γ x y 𝓁̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `≼
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ (` x) `≼ (` y) ⦂ `𝔹

  ⊢⊔ : ∀ {Γ x y 𝓁̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `⊔
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ (` x) `⊔ (` y) ⦂ `ℒ

  ⊢⊓ : ∀ {Γ x y 𝓁̂}
    → nth Γ x ≡ just `ℒ
    → nth Γ y ≡ just `ℒ
      --------------------------------- `⊓
    → Γ [ 𝓁̂ , 𝓁̂ ]⊢ (` x) `⊓ (` y) ⦂ `ℒ

  ⊢unlabel : ∀ {Γ x T 𝓁̂ 𝓁̂₁}
    → nth Γ x ≡ just (Lab 𝓁̂ T)
      -------------------------------------- Unlabel
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ⋎ 𝓁̂ ]⊢ unlabel (` x) ⦂ T

  ⊢to-label : ∀ {Γ T M 𝓁̂₁ 𝓁̂₂ 𝓁}
    → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T
    → 𝓁̂₂ ≾ ((l̂ 𝓁) ⋎ 𝓁̂₁)
      -------------------------------------- ToLab
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ to-label 𝓁 M ⦂ Lab (l̂ 𝓁) T

  ⊢to-label-dyn : ∀ {Γ x T M 𝓁̂₁ 𝓁̂₂}
    → nth Γ x ≡ just `ℒ
    → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T
      --------------------------------------------- ToLabDyn
    → Γ [ 𝓁̂₁ , 𝓁̂₁ ]⊢ to-label-dyn (` x) M ⦂ Lab ¿ T
