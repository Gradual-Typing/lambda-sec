module Interp where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)

data Cell : Set where
  _,_↦_ : ℒ̂ → ℒ̂ → Term → Cell

Store : Set
Store = List Cell

mutual
  -- A closure is a term with an env
  data Clos : Set where
    clos : Term → Env → Clos

  Env : Set
  Env = List Clos

-- Machine configuration after eval
Conf : Set
Conf = Store × Clos × ℒ̂

data Error : Set where
  stuck : Error
  castError : Error
  NSUError : Error
  storeOutofBound : Error

data Result (X : Set) : Set where
  error : Error → Result X
  result : X → Result X

-- Bind
_>>=_ : Result Conf → (Conf → Result Conf) → Result Conf
(error err) >>= _ = error err
(result x) >>= f = f x

𝒱 : ∀ {Γ T 𝓁̂₁ 𝓁̂₂} → (γ : Env) → (M : Term) → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → Store → (𝓁̂ : ℒ̂) → Result Conf
𝒱 γ `tt _ S 𝓁̂ = result ⟨ S , ⟨ clos `tt [] , 𝓁̂ ⟩ ⟩
𝒱 γ `true _ S 𝓁̂ = result ⟨ S , ⟨ clos `true [] , 𝓁̂ ⟩ ⟩
𝒱 γ `false _ S 𝓁̂ = result ⟨ S , ⟨ clos `false [] , 𝓁̂ ⟩ ⟩
𝒱 γ (label 𝓁) _ S 𝓁̂ = result ⟨ S , ⟨ clos (label 𝓁) [] , 𝓁̂ ⟩ ⟩
𝒱 γ (` x) _ S 𝓁̂ with nth γ x
... | nothing = error stuck
... | just c = result ⟨ S , ⟨ c , 𝓁̂ ⟩ ⟩
