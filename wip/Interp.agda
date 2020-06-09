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
open import Lemmas


-- Bind
_>>=_ : Result Conf → (Conf → Result Conf) → Result Conf
timeout >>= _ = timeout
error err >>= _ = error err
result x >>= f = f x

-- Cast 𝓁̂₁ ⇛ 𝓁̂₂
--   This can only happen where 𝓁̂₁ ⊑̂ 𝓁̂₂
castL : (m : Store) → (pc : ℒ) → (𝓁̂₁ 𝓁̂₂ : ℒ̂) → 𝓁̂₁ ⊑̂ 𝓁̂₂ → Result Conf
castL m pc 𝓁̂₁ 𝓁̂₂ 𝓁̂₁⊑̂𝓁̂₂ with (l̂ pc) ⊑̂? 𝓁̂₂
... | yes _ = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩
... | no  _ = error castError

-- Cast T ⇛ S
--   This can only happen when T₁ ≲ T₂
castT′ : (m : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → T₁ ≲ T₂ → (v : Value) → Result Conf
-- Unit ⇛ Unit
castT′ m pc `⊤ `⊤ ≲-⊤ V-tt         = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩  -- just return
castT′ m pc `⊤ `⊤ ≲-⊤ _            = error stuck                   -- stuck if the value is not well-typed
-- 𝔹 ⇛ 𝔹
castT′ m pc `𝔹 `𝔹 ≲-𝔹 V-true      = result ⟨ m , ⟨ V-true  , pc ⟩ ⟩
castT′ m pc `𝔹 `𝔹 ≲-𝔹 V-false     = result ⟨ m , ⟨ V-false , pc ⟩ ⟩
castT′ m pc `𝔹 `𝔹 ≲-𝔹 _           = error stuck
-- ℒ ⇛ ℒ
castT′ m pc `ℒ `ℒ ≲-ℒ (V-label 𝓁) = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩
castT′ m pc `ℒ `ℒ ≲-ℒ _            = error stuck
-- Ref ⇛ Ref
castT′ m pc (Ref 𝓁̂₁ T₁′) (Ref 𝓁̂₂ T₂′) (≲-Ref _ _ _ _) (V-ref n 𝓁₁ 𝓁₂) with 𝓁̂₂
... | ¿ = result ⟨ m , ⟨ V-ref n 𝓁₁ 𝓁₂ , pc ⟩ ⟩
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | no _ = error castError
...   | yes _ = result ⟨ m , ⟨ V-ref n 𝓁₁ 𝓁₂ , pc ⟩ ⟩
castT′ m pc (Ref 𝓁₁ T₁′) (Ref 𝓁₂ T₂′) (≲-Ref _ _ _ _) _ = error stuck
-- Labeled ⇛ Labeled
castT′ m pc (Lab 𝓁̂₁ T₁′) (Lab 𝓁̂₂ T₂′) (≲-Lab _ T₁′≲T₂′) (V-lab 𝓁 v) with (l̂ 𝓁) ⊑̂? 𝓁̂₂
... | no _ = error castError
... | yes _ =
  do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT′ m pc T₁′ T₂′ T₁′≲T₂′ v
  result ⟨ m′ , ⟨ (V-lab 𝓁 v′) , pc′ ⟩ ⟩
castT′ m pc (Lab 𝓁̂₁ T₁′) (Lab 𝓁̂₂ T₂′) (≲-Lab _ _) _ = error stuck
-- Closure ⇛ Proxied closure
--   NOTE: We need to build proxy here.
castT′ m pc (S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T) (S′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T′) (≲-⇒ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′ S′≲S T≲T′) v with v
... | (V-clos _) =
      result ⟨ m , ⟨ V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′  𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′ v , pc ⟩ ⟩
... | (V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _) =
      result ⟨ m , ⟨ V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′  v , pc ⟩ ⟩
... | _ = error stuck

-- Tests:

--   Get stuck when casting a bool value to a reference
_ : castT′ [] (l 0) (Ref ¿ `𝔹) (Ref ¿ `𝔹) (≲-Ref ⊑̂-¿-r ⊑̂-¿-r ≲-𝔹 ≲-𝔹) V-true ≡ error stuck
_ = refl

castT : (m : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → (v : Value) → Result Conf
castT m pc T₁ T₂ v with T₁ ≲? T₂
... | no  _     = error castError
... | yes T₁≲T₂ = castT′ m pc T₁ T₂ T₁≲T₂ v -- proceed


-- NOTE that pc must not be ¿ in run time!
𝒱 : ∀ {Γ T 𝓁̂₁ 𝓁̂₂} → (γ : Env) → (M : Term) → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → Store → (pc : ℒ) → (k : ℕ) → Result Conf
apply : Env → Value → Value → Store → (pc : ℒ) → (k : ℕ) → Result Conf

-- Running out of gas
𝒱 _ _ _ _ _ 0 = timeout

𝒱 γ `tt _ m pc (suc k) = result ⟨ m , ⟨ V-tt , pc ⟩ ⟩
𝒱 γ `true _ m pc (suc k) = result ⟨ m , ⟨ V-true , pc ⟩ ⟩
𝒱 γ `false _ m pc (suc k) = result ⟨ m , ⟨ V-false , pc ⟩ ⟩
𝒱 γ (label 𝓁) _ m pc (suc k) = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩

𝒱 γ (` x) _ m pc (suc k) with nth γ x
... | nothing = error stuck
... | just v = result ⟨ m , ⟨ v , pc ⟩ ⟩

𝒱 γ (if `x M N) (⊢if {x = x} {T} {T′} {T″} {M} {N} {𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) m pc (suc k) with nth γ x
--   : goes to the M branch
... | just V-true = do
  ⟨ m′ , ⟨ vₘ , pc′ ⟩ ⟩ ← 𝒱 γ M ⊢M m pc k
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂ (𝓁̂₂ ⊔̂ 𝓁̂₂′) 𝓁̂⊑̂𝓁̂⊔̂𝓁̂′
  castT m″ pc″ T T″ vₘ  -- cast T ⇛ T″ , where T ⋎ T′ ≡ T″
--   : goes to the N branch
... | just V-false = do
  ⟨ m′ , ⟨ vₙ , pc′ ⟩ ⟩ ← 𝒱 γ N ⊢N m pc k
  ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩ ← castL m′ pc′ 𝓁̂₂′ (𝓁̂₂ ⊔̂ 𝓁̂₂′) 𝓁̂⊑̂𝓁̂′⊔̂𝓁̂
  castT m″ pc″ T′ T″ vₙ -- cast T′ ⇛ T″ , where T ⋎ T′ ≡ T″
... | _ = error stuck

𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) m pc (suc k) with nth γ x
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) with lookup m loc 𝓁₁ 𝓁₂
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just ⟨ T′ , v ⟩ =
  castT m (pc ⊔ 𝓁₂) T′ T v  -- need to update pc
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | nothing =
  error memAccError
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) m pc (suc k) | _ = error stuck

𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) m pc (suc k) with nth γ x | nth γ y
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v with lookup m loc 𝓁₁ 𝓁₂
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v | just ⟨ T″ , _ ⟩ =
  do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m (pc ⊔ 𝓁₂) T′ T v  -- need to update pc because of the `get`
  ⟨ m″ , ⟨ v″ , pc″ ⟩ ⟩ ← castT m′ pc′ T T″ v′
  setmem m″ loc 𝓁₁ 𝓁₂ pc″ ⟨ T″ , v″ ⟩
  where
  setmem : (m : Store) → (loc : ℕ) → (𝓁₁ 𝓁₂ : ℒ) → (pc : ℒ) → 𝕋 × Value → Result Conf
  setmem m loc 𝓁₁ 𝓁₂ pc Tv with pc ⊑? 𝓁₂
  ... | yes _ = result ⟨ loc , 𝓁₁ , 𝓁₂ ↦ Tv ∷ m , ⟨ V-tt , pc ⟩ ⟩
  ... | no _ = error NSUError
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) m pc (suc k) | just (V-ref loc 𝓁₁ 𝓁₂) | just v | nothing =
  error memAccError
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) m pc (suc k) | _ | _ = error stuck

𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) m pc (suc k) with pc ⊑? 𝓁
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) m pc (suc k) | yes _ with nth γ y
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) m pc (suc k) | yes _ | just v =
  let loc = length m in
    result ⟨ loc , pc , 𝓁 ↦ ⟨ T , v ⟩ ∷ m , ⟨ V-ref loc pc 𝓁 , pc ⟩ ⟩
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) m pc (suc k) | yes _ | nothing = error stuck
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) m pc (suc k) | no _ = error NSUError

-- `new-dyn` is similar to `new` except that 𝓁 comes into play at runtime (instead of from typing derivation).
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) m pc (suc k) with nth γ x | nth γ y
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) m pc (suc k) | just (V-label 𝓁) | just v with pc ⊑? 𝓁
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) m pc (suc k) | just (V-label 𝓁) | just v | yes _ =
  let loc = length m in
    result ⟨ loc , pc , 𝓁 ↦ ⟨ T , v ⟩ ∷ m , ⟨ V-ref loc pc 𝓁 , pc ⟩ ⟩
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) m pc (suc k) | just (V-label 𝓁) | just v | no _ =
  error NSUError
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) m pc (suc k) | _ | _ = error stuck

𝒱 γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} _ _ _ _) m pc (suc k) with nth γ x | nth γ y
... | just (V-ref loc 𝓁₁ 𝓁₂) | just (V-ref loc′ 𝓁₁′ 𝓁₂′) =
  result ⟨ m , ⟨ =?-ref loc loc′ 𝓁₁ 𝓁₁′ 𝓁₂ 𝓁₂′ , pc ⟩ ⟩
  where
  =?-ref : (loc loc′ : ℕ) → (𝓁₁ 𝓁₁′ 𝓁₂ 𝓁₂′ : ℒ) → Value
  =?-ref loc loc′ 𝓁₁ 𝓁₁′ 𝓁₂ 𝓁₂′ with loc ≟ₙ loc′ | 𝓁₁ ≟ 𝓁₁′ | 𝓁₂ ≟ 𝓁₂′
  ... | yes _ | yes _ | yes _ = V-true
  ... | _     | _     | _     = V-false
... | _ | _ = error stuck

-- Let binding
𝒱 {Γ} γ (`let M N) (⊢let {T = T} {T′} {S} {M} {N} ⊢M ⊢N T′≲T) m pc (suc k) = do
  ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← 𝒱 {Γ} γ M ⊢M m pc k
  ⟨ m″ , ⟨ v″ , pc″ ⟩ ⟩ ← castT m′ pc′ T′ T v′ -- need to cast T′ ⇛ T
  𝒱 {T ∷ Γ} (v″ ∷ γ) N ⊢N m″ pc″ k

-- Lambda abstraction
𝒱 γ (ƛ N) (⊢ƛ ⊢N) m pc (suc k) = result ⟨ m , ⟨ V-clos < N , γ , ⊢N > , pc ⟩ ⟩

𝒱 γ (ref-label `x) (⊢ref-label {x = x} _) m pc (suc k) with nth γ x
... | just (V-ref loc 𝓁₁ 𝓁₂) = result ⟨ m , ⟨ V-label 𝓁₂ , pc ⟩ ⟩ -- return 𝓁₂ since 𝓁₁ is the saved pc
... | _ = error stuck

𝒱 γ (lab-label `x) (⊢lab-label {x = x} _) m pc (suc k) with nth γ x
... | just (V-lab 𝓁 v) = result ⟨ m , ⟨ V-label 𝓁 , pc ⟩ ⟩
... | _ = error stuck

𝒱 γ pc-label ⊢pc-label m pc (suc k) = result ⟨ m , ⟨ V-label pc , pc ⟩ ⟩

𝒱 γ (`x `⊔ `y) (⊢⊔ {x = x} {y} _ _) m pc (suc k) with nth γ x | nth γ y
... | just (V-label 𝓁x) | just (V-label 𝓁y) = result ⟨ m , ⟨ V-label (𝓁x ⊔ 𝓁y) , pc ⟩ ⟩
... | _ | _ = error stuck

𝒱 γ (`x `⊓ `y) (⊢⊓ {x = x} {y} _ _) m pc (suc k) with nth γ x | nth γ y
... | just (V-label 𝓁x) | just (V-label 𝓁y) = result ⟨ m , ⟨ V-label (𝓁x ⊓ 𝓁y) , pc ⟩ ⟩
... | _ | _ = error stuck

𝒱 γ (`x `⊑ `y) (⊢⊑ {x = x} {y} _ _) m pc (suc k) with nth γ x | nth γ y
𝒱 γ (`x `⊑ `y) (⊢⊑ {x = x} {y} _ _) m pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) with 𝓁x ⊑? 𝓁y
𝒱 γ (`x `⊑ `y) (⊢⊑ {x = x} {y} _ _) m pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) | yes _ =
  result ⟨ m , ⟨ V-true , pc ⟩ ⟩
𝒱 γ (`x `⊑ `y) (⊢⊑ {x = x} {y} _ _) m pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) | no  _ =
  result ⟨ m , ⟨ V-false , pc ⟩ ⟩
𝒱 γ (`x `⊑ `y) (⊢⊑ {x = x} {y} _ _) m pc (suc k) | _ | _ = error stuck

𝒱 γ (unlabel `x) (⊢unlabel {x = x} _) m pc (suc k) with nth γ x
... | just (V-lab 𝓁 v) = result ⟨ m , ⟨ v , pc ⊔ 𝓁 ⟩ ⟩ -- need to update pc
... | _ = error stuck

𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) with 𝒱 γ M ⊢M m pc k
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ with pc′ ⊑? (pc ⊔ 𝓁)
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ | yes _ =
  result ⟨ m′ , ⟨ V-lab 𝓁 v , pc ⟩ ⟩
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) | error err = error err
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) m pc (suc k) | timeout = timeout

-- Similar to `to-label` except that 𝓁 comes into play at runtime
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) with nth γ x
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) with 𝒱 γ M ⊢M m pc k
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ with pc′ ⊑? (pc ⊔ 𝓁)
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ | yes _ =
  result ⟨ m′ , ⟨ V-lab 𝓁 v , pc ⟩ ⟩
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) | result ⟨ m′ , ⟨ v , pc′ ⟩ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) | error err = error err
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | just (V-label 𝓁) | timeout = timeout
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) m pc (suc k) | _ = error stuck

-- Application
𝒱 γ (`x · `y) (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} _ _ _ 𝓁̂₁′⊑̂𝓁̂₁) m pc (suc k)
    with nth γ x | nth γ y
... | just v | just w = do
    ⟨ m′ , ⟨ v′ , pc′ ⟩ ⟩ ← castT m pc T′ T w           -- cast T′ ⇛ T
    ⟨ m″ , ⟨ _ , pc″ ⟩ ⟩  ← castL m′ pc′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′⊑̂𝓁̂₁  -- cast 𝓁̂₁′ ⇛ 𝓁̂₁
    apply γ v w m pc k
... | _ | _ = error stuck

apply γ (V-clos < N , ρ , ⊢N >) w m pc k = 𝒱 (w ∷ ρ) N ⊢N m pc k
apply γ (V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′⊑̂𝓁̂₁ 𝓁̂₂⊑̂𝓁̂₂′ v) w m pc k = do
    ⟨ m₁ , ⟨ w′ , pc₁ ⟩ ⟩ ← castT m pc S′ S w           -- cast S′ ⇛ S
    ⟨ m₁ , ⟨ _ ,  pc₁ ⟩ ⟩ ← castL m₁ pc₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′⊑̂𝓁̂₁  -- cast 𝓁̂₁′ ⇛ 𝓁̂₁
    ⟨ m₂ , ⟨ v₁ , pc₂ ⟩ ⟩ ← apply γ v w′ m₁ pc₁ k
    ⟨ m₂ , ⟨ _ ,  pc₂ ⟩ ⟩ ← castL m₂ pc₂ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂⊑̂𝓁̂₂′  -- cast 𝓁̂₂ ⇛ 𝓁̂₂′
    castT m₂ pc₂ T T′ v₁                                 -- cast T ⇛ T′
apply γ _ w m pc k = error stuck
