module Interp where

open import Data.Nat using (ℕ; zero; suc; _≤_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

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
    <_,_> : Term → Env → Clos

  data Value : Set where
    V-tt : Value

    V-true : Value
    V-false : Value

    V-label : ℒ → Value

    V-clos : Clos → Value
    V-proxy : (T T′ S S′ : 𝕋) → (𝓁̂₁ 𝓁̂₁′ 𝓁̂₂ 𝓁̂₂′ : ℒ̂) → Clos → Value

    V-ref : ℕ → ℒ → ℒ → Value

    V-lab : ℒ → Value → Value

  Env : Set
  Env = List Value


-- Machine configuration after eval
Conf : Set
Conf = Store × Value × ℒ

data Error : Set where
  stuck : Error
  castError : Error
  NSUError : Error
  storeOutofBound : Error

-- The evaluation either diverges, or runs into an error, or returns a value.
data Result (X : Set) : Set where
  diverge : Result X
  error : Error → Result X
  result : X → Result X

-- Bind
_>>=_ : Result Conf → (Conf → Result Conf) → Result Conf
diverge >>= _ = diverge
error err >>= _ = error err
result x >>= f = f x

-- Cast 𝓁̂₁ ⇛ 𝓁̂₂
--   This can only happen where 𝓁̂₁ ⊑̂ 𝓁̂₂

castL : (m : Store) → (pc : ℒ) → (𝓁̂₁ 𝓁̂₂ : ℒ̂) → Result Conf
castL m pc 𝓁̂₁ 𝓁̂₂ with 𝓁̂₁ ⊑̂? 𝓁̂₂
... | no _ = error castError
... | yes _ with (l̂ pc) ⊑̂? 𝓁̂₂
...   | no _ = error castError
...   | yes _ = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩

-- Cast T ⇛ S
--   This can only happen when T₁ ≲ T₂

castT′ : (m : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → (v : Value) → Result Conf
-- Unit ⇛ Unit
castT′ m pc `⊤ `⊤ V-tt         = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩  -- just return
-- 𝔹 ⇛ 𝔹
castT′ m pc `𝔹 `𝔹 V-true      = result ⟨ m , ⟨ V-true  , pc ⟩ ⟩
castT′ m pc `𝔹 `𝔹 V-false     = result ⟨ m , ⟨ V-false , pc ⟩ ⟩
-- ℒ ⇛ ℒ
castT′ m pc `ℒ `ℒ (V-label 𝓁) = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩
-- Ref ⇛ Ref
castT′ m pc (Ref 𝓁̂₁ T₁′) (Ref 𝓁̂₂ T₂′) (V-ref n 𝓁₁ 𝓁₂) with 𝓁̂₂
... | ¿ = result ⟨ m , ⟨ V-ref n 𝓁₁ 𝓁₂ , pc ⟩ ⟩
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | no _ = error castError
...   | yes _ = result ⟨ m , ⟨ V-ref n 𝓁₁ 𝓁₂ , pc ⟩ ⟩
-- Labeled ⇛ Labeled
castT′ m pc (Lab 𝓁̂₁ T₁′) (Lab 𝓁̂₂ T₂′) (V-lab 𝓁 v) with (l̂ 𝓁) ⊑̂? 𝓁̂₂
... | no _ = error castError
... | yes _ = castT′ m pc T₁′ T₂′ v >>= λ { ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ → result ⟨ m′ , ⟨ (V-lab 𝓁 v′) , pc′ ⟩ ⟩ }
-- Closure ⇛ Proxied closure
--   NOTE: We need to build proxy here.
castT′ m pc (T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S) (T′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] S′) (V-clos < M , ρ >) =
  result ⟨ m , ⟨ V-proxy T T′ S S′ 𝓁̂₁ 𝓁̂₁′ 𝓁̂₂ 𝓁̂₂′ < M , ρ > , pc ⟩ ⟩
-- The default case is stuck.
castT′ m pc _ _ _ = error stuck


-- Tests:
--   Get stuck when casting from a reference to a bool:
_ : castT′ [] (l 0) (Ref ¿ `𝔹) `𝔹 V-true ≡ error stuck
_ = refl

--   Get stuck when casting a bool value to a reference
_ : castT′ [] (l 0) (Ref ¿ `𝔹) (Ref ¿ `𝔹) V-true ≡ error stuck
_ = refl

castT : (m : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → (v : Value) → Result Conf
castT m pc T₁ T₂ v with T₁ ≲? T₂
... | no  _ = error castError
... | yes _ = castT′ m pc T₁ T₂ v -- proceed


-- NOTE that pc must not be ¿ in run time!
𝒱 : ∀ {Γ T 𝓁̂₁ 𝓁̂₂} → (γ : Env) → (M : Term) → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → Store → (pc : ℒ) → Result Conf
𝒱 γ `tt _ m pc = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩
𝒱 γ `true _ m pc = result ⟨ m , ⟨ V-true , pc ⟩ ⟩
𝒱 γ `false _ m pc = result ⟨ m , ⟨ V-false , pc ⟩ ⟩
𝒱 γ (label 𝓁) _ m pc = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩
𝒱 γ (` x) _ m pc with nth γ x
... | nothing = error stuck
... | just v = result ⟨ m , ⟨ v , pc ⟩ ⟩
𝒱 {Γ} γ (if `x M N) (⊢if {x = x} {T} {T′} {T″} {M} {N} {𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq₁ ⊢M ⊢N eq₂) m pc with nth γ x
-- goes to the M branch
... | just V-true = do
  ⟨ m′ , ⟨ vₘ , pc′ ⟩ ⟩ ← 𝒱 γ M ⊢M m pc
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂ (𝓁̂₂ ⊔̂ 𝓁̂₂′)
  castT m″ pc″ T T″ vₘ  -- cast T ⇛ T″ , where T ⋎ T′ ≡ T″
-- goes to the N branch
... | just V-false = do
  ⟨ m′ , ⟨ vₙ , pc′ ⟩ ⟩ ← 𝒱 γ N ⊢N m pc
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂′ (𝓁̂₂ ⊔̂ 𝓁̂₂′)
  castT m″ pc″ T′ T″ vₙ -- cast T′ ⇛ T″ , where T ⋎ T′ ≡ T″
... | _ = error stuck
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc = {!!}
