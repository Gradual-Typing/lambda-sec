module Interp where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import StaticsLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Memory



-- Bind
_>>=_ : Result Conf → (Conf → Result Conf) → Result Conf
timeout >>= _ = timeout
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
-- FIXME: Rule out the stuck case by adding a premise T₁ ≲ T₂
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
castT′ m pc (T [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S) (T′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] S′) (V-clos clos) =
  result ⟨ m , ⟨ V-proxy T T′ S S′ 𝓁̂₁ 𝓁̂₁′ 𝓁̂₂ 𝓁̂₂′ clos , pc ⟩ ⟩
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
𝒱 : ∀ {Γ T 𝓁̂₁ 𝓁̂₂} → (γ : Env) → (M : Term) → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → Store → (pc : ℒ) → (k : ℕ) → Result Conf
𝒱 _ _ _ _ _ 0 = timeout
𝒱 γ `tt _ m pc (suc k) = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩
𝒱 γ `true _ m pc (suc k) = result ⟨ m , ⟨ V-true , pc ⟩ ⟩
𝒱 γ `false _ m pc (suc k) = result ⟨ m , ⟨ V-false , pc ⟩ ⟩
𝒱 γ (label 𝓁) _ m pc (suc k) = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩
𝒱 γ (` x) _ m pc (suc k) with nth γ x
... | nothing = error stuck
... | just v = result ⟨ m , ⟨ v , pc ⟩ ⟩
𝒱 {Γ} γ (if `x M N) (⊢if {x = x} {T} {T′} {T″} {M} {N} {𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} eq₁ ⊢M ⊢N eq₂) m pc (suc k) with nth γ x
-- goes to the M branch
... | just V-true = do
  ⟨ m′ , ⟨ vₘ , pc′ ⟩ ⟩ ← 𝒱 γ M ⊢M m pc k
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂ (𝓁̂₂ ⊔̂ 𝓁̂₂′)
  castT m″ pc″ T T″ vₘ  -- cast T ⇛ T″ , where T ⋎ T′ ≡ T″
-- goes to the N branch
... | just V-false = do
  ⟨ m′ , ⟨ vₙ , pc′ ⟩ ⟩ ← 𝒱 γ N ⊢N m pc k
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂′ (𝓁̂₂ ⊔̂ 𝓁̂₂′)
  castT m″ pc″ T′ T″ vₙ -- cast T′ ⇛ T″ , where T ⋎ T′ ≡ T″
... | _ = error stuck
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc (suc k) with nth γ x
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) with lookup m loc 𝓁₁ 𝓁₂
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just ⟨ T′ , v ⟩ = castT m (pc ⊔ 𝓁₂) T′ T v  -- need to upgrade pc
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | nothing = error memAccError
𝒱 {Γ} γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} eq) m pc (suc k) | _ = error stuck
𝒱 {Γ} γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} {𝓁̂} eq₁ eq₂ T′≲T 𝓁̂₁⊑̂𝓁̂ ) m pc (suc k) with nth γ x | nth γ y
𝒱 {Γ} γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} {𝓁̂} eq₁ eq₂ T′≲T 𝓁̂₁⊑̂𝓁̂ ) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v with lookup m loc 𝓁₁ 𝓁₂
𝒱 {Γ} γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} {𝓁̂} eq₁ eq₂ T′≲T 𝓁̂₁⊑̂𝓁̂ ) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v | just ⟨ T″ , _ ⟩ = do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m (pc ⊔ 𝓁₂) T′ T v  -- need to upgrade pc because of the `get`
  ⟨ m″ , ⟨ v″ , pc″ ⟩ ⟩ ← castT m′ pc′ T T″ v′
  setmem m″ loc 𝓁₁ 𝓁₂ pc″ ⟨ T″ , v″ ⟩
  where
  setmem : (m : Store) → (loc : ℕ) → (𝓁₁ 𝓁₂ : ℒ) → (pc : ℒ) → 𝕋 × Value → Result Conf
  setmem m loc 𝓁₁ 𝓁₂ pc Tv with pc ⊑? 𝓁₂
  ... | yes _ = result ⟨ loc , 𝓁₁ , 𝓁₂ ↦ Tv ∷ m , ⟨ V-tt , pc ⟩ ⟩
  ... | no _ = error NSUError
𝒱 {Γ} γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} {𝓁̂} eq₁ eq₂ T′≲T 𝓁̂₁⊑̂𝓁̂ ) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v | nothing = error memAccError
𝒱 {Γ} γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} {𝓁̂} eq₁ eq₂ T′≲T 𝓁̂₁⊑̂𝓁̂ ) m pc (suc k) | _ | _ = error stuck
𝒱 {Γ} γ (new 𝓁 `y) (⊢new {y = y} {T} {𝓁̂₁} {𝓁} eq 𝓁̂₁⊑̂𝓁) m pc (suc k) with pc ⊑? 𝓁
𝒱 {Γ} γ (new 𝓁 `y) (⊢new {y = y} {T} {𝓁̂₁} {𝓁} eq 𝓁̂₁⊑̂𝓁) m pc (suc k) | yes _ with nth γ y
𝒱 {Γ} γ (new 𝓁 `y) (⊢new {y = y} {T} {𝓁̂₁} {𝓁} eq 𝓁̂₁⊑̂𝓁) m pc (suc k) | yes _ | just v =
  let loc = length m in result ⟨ loc , pc , 𝓁 ↦ ⟨ T , v ⟩ ∷ m , ⟨ V-ref loc pc 𝓁 , pc ⟩ ⟩
𝒱 {Γ} γ (new 𝓁 `y) (⊢new {y = y} {T} {𝓁̂₁} {𝓁} eq 𝓁̂₁⊑̂𝓁) m pc (suc k) | yes _ | nothing = error stuck
𝒱 {Γ} γ (new 𝓁 `y) (⊢new {y = y} {T} {𝓁̂₁} {𝓁} eq 𝓁̂₁⊑̂𝓁) m pc (suc k) | no _ = error NSUError
-- `new-dyn` is similar to `new` except that 𝓁 comes into play at runtime (instead of from typing derivation).
𝒱 {Γ} γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} {𝓁̂₁} eq₁ eq₂) m pc (suc k) with nth γ x | nth γ y
𝒱 {Γ} γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} {𝓁̂₁} eq₁ eq₂) m pc (suc k) | just (V-label 𝓁) | just v with pc ⊑? 𝓁
𝒱 {Γ} γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} {𝓁̂₁} eq₁ eq₂) m pc (suc k) | just (V-label 𝓁) | just v | yes _ =
  let loc = length m in result ⟨ loc , pc , 𝓁 ↦ ⟨ T , v ⟩ ∷ m , ⟨ V-ref loc pc 𝓁 , pc ⟩ ⟩
𝒱 {Γ} γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} {𝓁̂₁} eq₁ eq₂) m pc (suc k) | just (V-label 𝓁) | just v | no _ = error NSUError
𝒱 {Γ} γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} {𝓁̂₁} eq₁ eq₂) m pc (suc k) | _ | _ = error stuck
𝒱 {Γ} γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} eq₁ eq₂ _ _) m pc (suc k) with nth γ x | nth γ y
𝒱 {Γ} γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} eq₁ eq₂ _ _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just (V-ref loc′ 𝓁₁′ 𝓁₂′)
  with loc ≟ₙ loc′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
𝒱 {Γ} γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} eq₁ eq₂ _ _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just (V-ref loc′ 𝓁₁′ 𝓁₂′) | yes _ | yes _ | yes _ =
  result ⟨ m , ⟨ V-true , pc ⟩ ⟩
𝒱 {Γ} γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} eq₁ eq₂ _ _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just (V-ref loc′ 𝓁₁′ 𝓁₂′) | _ | _ | _ =
  result ⟨ m , ⟨ V-false , pc ⟩ ⟩
𝒱 {Γ} γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} eq₁ eq₂ _ _) m pc (suc k) | _ | _ = error stuck
-- Let binding
𝒱 {Γ} γ (`let M N) (⊢let {T = T} {T′} {S} {M} {N} ⊢M ⊢N T′≲T) m pc (suc k) = do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← 𝒱 {Γ} γ M ⊢M m pc k
  ⟨ m″ , ⟨ v″ , pc″ ⟩ ⟩ ← castT m′ pc′ T′ T v′ -- need to cast T′ ⇛ T
  𝒱 {T ∷ Γ} (v″ ∷ γ) N ⊢N m″ pc″ k
-- Lambda abstraction
𝒱 {Γ} γ (ƛ N) (⊢ƛ {T = T} {S} {N} {𝓁̂₁} {𝓁̂₂} {𝓁} ⊢N) m pc (suc k) =
  result ⟨ m , ⟨ V-clos < N , γ , ⊢N > , pc ⟩ ⟩
𝒱 {Γ} γ (`x · `y) (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} {𝓁̂₂} _ _ _ _) m pc (suc k) with nth γ x | nth γ y
... | just (V-clos < N , ρ , ⊢N >) | just v = do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m pc T′ T v  -- cast T′ ⇛ T
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₁′ 𝓁̂₁ -- cast 𝓁̂₁′ ⇛ 𝓁̂₁
  𝒱 (v′ ∷ ρ) N ⊢N m″ pc″ k
... | just (V-proxy T″ T‴ S″ S‴ 𝓁̂₁″ 𝓁̂₁‴ 𝓁̂₂″ 𝓁̂₂‴ < N , ρ , ⊢N >) | just v = do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m pc T′ T v
  ⟨ m′ , ⟨ _ , pc′ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₁′ 𝓁̂₁
  -- dive into the proxy
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m′ pc′ T″ T‴ v′
  ⟨ m′ , ⟨ _ , pc′ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₁″ 𝓁̂₁‴
  ⟨ m″ , ⟨ v″ , pc″ ⟩ ⟩ ← 𝒱 (v′ ∷ ρ) N ⊢N m′ pc′ k
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m″ pc″ 𝓁̂₂″ 𝓁̂₂‴
  castT m″ pc″ S″ S‴ v″
... | _ | _ = error stuck
