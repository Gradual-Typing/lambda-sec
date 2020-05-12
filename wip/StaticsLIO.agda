module StaticsLIO where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s) renaming (_⊔_ to _⊔ₙ_)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_)
open import Data.Maybe
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
import Syntax

infixr 6 _[_]⇒[_]_
infixl 7 _·_
infixl 8 _`⊔_  -- join
infixl 8 _`⊓_  -- meet
infixl 9 _`⊑_  -- label leq

data ℒ : Set where
  l : ℕ → ℒ

data ℒ̂ : Set where
  ¿ : ℒ̂
  l̂ : ℒ → ℒ̂

-- Examples: low and high.
𝐿 : ℒ̂
𝐿 = l̂ (l 0)

𝐻 : ℒ̂
𝐻 = l̂ (l 1)

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
  op-lam : ℒ̂ → Op
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
sig op-if       = 0 ∷ 0 ∷ []
sig (op-lam 𝓁̂)  = 1 ∷ []
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
pattern `if  M N = op-if  ⦅ cons (ast M) (cons (ast N) nil) ⦆
pattern ƛ 𝓁̂ N = (op-lam 𝓁̂) ⦅ cons (bind (ast N)) nil ⦆
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
pattern _`⊑_ `x `y = op-label-leq ⦅ cons (ast `x) (cons (ast `y) nil) ⦆
pattern unlabel `x = op-unlabel ⦅ cons (ast `x) nil ⦆
pattern to-label 𝓁 M = (op-to-label 𝓁) ⦅ cons (ast M) nil ⦆
pattern to-label-dyn `x M = op-to-label-dyn ⦅ cons (ast `x) (cons (ast M) nil) ⦆

-- partial ordering of labels
infixl 9 _⊑_
infixl 9 _⊑̂_

data _⊑_ : ℒ → ℒ → Set where

  ⊑-l : ∀ {n , n′ : ℕ}
      → n ≤ n′
      → (l n) ⊑ (l n′)

data _⊑̂_ : ℒ̂ → ℒ̂ → Set where

  ⊑̂-¿-r : ∀ {𝓁̂} → 𝓁̂ ⊑̂ ¿

  ⊑̂-¿-l : ∀ {𝓁̂} → ¿ ⊑̂ 𝓁̂

  ⊑̂-l : ∀ {𝓁₁ 𝓁₂ : ℒ} → (l̂ 𝓁₁) ⊑̂ (l̂ 𝓁₂)

-- Consistent subtyping
infixl 9 _<:_

data _<:_ : 𝕋 → 𝕋 → Set where

  <:-⊤ :
    --------
    `⊤ <: `⊤

  <:-𝔹 :
    ---------
    `𝔹 <: `𝔹

  <:-ℒ :
    ---------
    `ℒ <: `ℒ

  <:-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ⊑̂ 𝓁̂₂
    → 𝓁̂₂ ⊑̂ 𝓁̂₁
    → T₁ <: T₂
    → T₂ <: T₁
      ----------------------
    → Ref 𝓁̂₁ T₁ <: Ref 𝓁̂₂ T₂

  <:-Lab : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ⊑̂ 𝓁̂₂
    → T₁ <: T₂
      ----------------------
    → Lab 𝓁̂₁ T₂ <: Lab 𝓁̂₂ T₂

  <:-⇒ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ T₁ T₂ T₁′ T₂′}
    → 𝓁̂₁′ ⊑̂ 𝓁̂₁
    → 𝓁̂₂  ⊑̂ 𝓁̂₂′
    → T₁′ <: T₁
    → T₂  <: T₂′
      --------------------------------------------------
    → (T₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T₂) <: (T₁′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂′)

-- Typing judgements
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
    → T′ <: T
    → Γ [ 𝓁̂₁ , 𝓁̂₃ ]⊢ `let M N ⦂ S
