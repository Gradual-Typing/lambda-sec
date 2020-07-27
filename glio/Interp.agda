module Interp where

open import Data.Nat using (ℕ; zero; suc; _≤_)
open import Data.Nat.Properties renaming (_≟_ to _≟ₙ_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; cong; cong₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)

open import StaticsGLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Store
open import Lemmas



-- Machine configuration after eval
Conf : Set
Conf = Store × Value × ℒ

data Error : Set where
  stuck : Error
  castError : Error
  NSUError : Error
  -- memAccError : Error -- Use stuck instead!

-- The evaluation either diverges (timeout), or runs into an error, or returns a value.
data Result (X : Set) : Set where
  timeout : Result X
  error : Error → Result X
  result : X → Result X

-- Bind
_>>=_ : Result Conf → (Conf → Result Conf) → Result Conf
timeout >>= _ = timeout
error err >>= _ = error err
result x >>= f = f x


-- Cast 𝓁̂₁ ⇛ 𝓁̂₂
--   This can only happen where 𝓁̂₁ ≾ 𝓁̂₂
castL : (μ : Store) → (pc : ℒ) → (𝓁̂₁ 𝓁̂₂ : ℒ̂) → 𝓁̂₁ ≾ 𝓁̂₂ → Result Conf
castL μ pc 𝓁̂₁ 𝓁̂₂ 𝓁̂₁≾𝓁̂₂ with (l̂ pc) ≾? 𝓁̂₂
... | yes _ = result ⟨ μ , V-tt , pc ⟩
... | no  _ = error castError

-- Cast T ⇛ S
--   This can only happen when T₁ ≲ T₂
castT′ : (μ : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → T₁ ≲ T₂ → (v : Value) → Result Conf
-- Unit ⇛ Unit
castT′ μ pc `⊤ `⊤ ≲-⊤ V-tt         = result ⟨ μ , V-tt , pc ⟩  -- just return
castT′ μ pc `⊤ `⊤ ≲-⊤ _            = error stuck                   -- stuck if the value is not well-typed
-- 𝔹 ⇛ 𝔹
castT′ μ pc `𝔹 `𝔹 ≲-𝔹 V-true      = result ⟨ μ , V-true , pc ⟩
castT′ μ pc `𝔹 `𝔹 ≲-𝔹 V-false     = result ⟨ μ , V-false , pc ⟩
castT′ μ pc `𝔹 `𝔹 ≲-𝔹 _           = error stuck
-- ℒ ⇛ ℒ
castT′ μ pc `ℒ `ℒ ≲-ℒ (V-label 𝓁) = result ⟨ μ , V-label 𝓁 , pc ⟩
castT′ μ pc `ℒ `ℒ ≲-ℒ _            = error stuck
-- Ref ⇛ Ref
castT′ μ pc (Ref 𝓁̂₁ T₁′) (Ref 𝓁̂₂ T₂′) (≲-Ref _ _ _ _) (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) with 𝓁̂₂
... | ¿ = result ⟨ μ , V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ , pc ⟩
... | (l̂ 𝓁₂′) with 𝓁₂ ≟ 𝓁₂′
...   | no _ = error castError
...   | yes _ = result ⟨ μ , V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩ , pc ⟩
castT′ μ pc (Ref 𝓁₁ T₁′) (Ref 𝓁₂ T₂′) (≲-Ref _ _ _ _) _ = error stuck
-- Labeled ⇛ Labeled
castT′ μ pc (Lab 𝓁̂₁ T₁′) (Lab 𝓁̂₂ T₂′) (≲-Lab _ T₁′≲T₂′) (V-lab 𝓁 v) with (l̂ 𝓁) ≾? 𝓁̂₂
... | no _ = error castError
... | yes _ =
  do
  ⟨ μ′ , v′ , pc′ ⟩ ← castT′ μ pc T₁′ T₂′ T₁′≲T₂′ v
  result ⟨ μ′ , V-lab 𝓁 v′ , pc′ ⟩
castT′ μ pc (Lab 𝓁̂₁ T₁′) (Lab 𝓁̂₂ T₂′) (≲-Lab _ _) _ = error stuck
-- Closure ⇛ Proxied closure
--   NOTE: We need to build proxy here.
castT′ μ pc (S [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] T) (S′ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T′) (≲-⇒ 𝓁̂₁′≾𝓁̂₁ 𝓁̂₂≾𝓁̂₂′ S′≲S T≲T′) v with v
... | (V-clos _) =
      result ⟨ μ , V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′  𝓁̂₁′≾𝓁̂₁ 𝓁̂₂≾𝓁̂₂′ v , pc ⟩
... | (V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _) =
      result ⟨ μ , V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′≾𝓁̂₁ 𝓁̂₂≾𝓁̂₂′  v , pc ⟩
... | _ = error stuck

-- Tests:

--   Get stuck when casting a bool value to a reference
_ : castT′ [] (l 0) (Ref ¿ `𝔹) (Ref ¿ `𝔹) (≲-Ref ≾-¿-r ≾-¿-r ≲-𝔹 ≲-𝔹) V-true ≡ error stuck
_ = refl

castT : (μ : Store) → (pc : ℒ) → (T₁ T₂ : 𝕋) → (v : Value) → Result Conf
castT μ pc T₁ T₂ v with T₁ ≲? T₂
... | no  _     = error castError
... | yes T₁≲T₂ = castT′ μ pc T₁ T₂ T₁≲T₂ v -- proceed


-- NOTE that pc must not be ¿ in run time!
𝒱 : ∀ {Γ T 𝓁̂₁ 𝓁̂₂} → (γ : Env) → (M : Term) → Γ [ 𝓁̂₁ , 𝓁̂₂ ]⊢ M ⦂ T → (μ : Store) → (pc : ℒ) → (k : ℕ) → Result Conf
apply : Env → Value → Value → Store → (pc : ℒ) → (k : ℕ) → Result Conf

-- Running out of gas
𝒱 _ _ _ _ _ 0 = timeout

𝒱 γ `tt _       μ pc (suc k) = result ⟨ μ , V-tt , pc ⟩
𝒱 γ `true _     μ pc (suc k) = result ⟨ μ , V-true , pc ⟩
𝒱 γ `false _    μ pc (suc k) = result ⟨ μ , V-false , pc ⟩
𝒱 γ (label 𝓁) _ μ pc (suc k) = result ⟨ μ , V-label 𝓁 , pc ⟩

𝒱 γ (` x) _ μ pc (suc k) with nth γ x
... | nothing = error stuck
... | just v = result ⟨ μ , v , pc ⟩

𝒱 γ (if `x M N) (⊢if {x = x} {T} {T′} {T″} {M} {N} {𝓁̂₁} {𝓁̂₂} {𝓁̂₂′} _ ⊢M ⊢N _) μ pc (suc k) with nth γ x
--   : goes to the M branch
... | just V-true = do
  ⟨ μ′ , vₘ , pc′ ⟩ ← 𝒱 γ M ⊢M μ pc k
  ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ 𝓁̂₂ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂⋎𝓁̂′
  castT μ″ pc″ T T″ vₘ  -- cast T ⇛ T″ , where T ∨ T′ ≡ T″
--   : goes to the N branch
... | just V-false = do
  ⟨ μ′ , vₙ , pc′ ⟩ ← 𝒱 γ N ⊢N μ pc k
  ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ 𝓁̂₂′ (𝓁̂₂ ⋎ 𝓁̂₂′) 𝓁̂≾𝓁̂′⋎𝓁̂
  castT μ″ pc″ T′ T″ vₙ -- cast T′ ⇛ T″ , where T ∨ T′ ≡ T″
... | _ = error stuck

𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) μ pc (suc k) with nth γ x
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) μ pc (suc k) | just (V-ref loc) with lookup μ loc
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) μ pc (suc k) | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) | just ⟨ T′ , v ⟩ =
  castT μ (pc ⊔ 𝓁₂) T′ T v  -- need to update pc
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) μ pc (suc k) | just (V-ref loc) | nothing =
  -- error memAccError
  error stuck
𝒱 γ (get `x) (⊢get {x = x} {T} {𝓁̂₁} {𝓁̂} _) μ pc (suc k) | _ = error stuck

𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref loc) | just v with lookup μ loc
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) | just v | just ⟨ T″ , _ ⟩ =
  do
  ⟨ μ′ , v′ , pc′ ⟩ ← castT μ (pc ⊔ 𝓁₂) T′ T v  -- need to update pc because of the `get`
  ⟨ μ″ , v″ , pc″ ⟩ ← castT μ′ pc′ T T″ v′
  setmem μ″ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ pc″ ⟨ T″ , v″ ⟩
  where
  setmem : (μ : Store) → (loc : Location) → (pc : ℒ) → 𝕋 × Value → Result Conf
  setmem μ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ pc Tv with pc ≼? 𝓁₂
  ... | yes _ = result ⟨ ⟨ n , 𝓁₁ , 𝓁₂ ⟩ ↦ Tv ∷ μ , V-tt , pc ⟩
  ... | no _ = error NSUError
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref loc) | just v | nothing =
  -- error memAccError
  error stuck
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {𝓁̂₁} _ _ T′≲T _) μ pc (suc k) | _ | _ = error stuck

𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) μ pc (suc k) with pc ≼? 𝓁
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ with nth γ y
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ | just v =
  let n = length μ in
    result ⟨ ⟨ n , pc , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ , V-ref ⟨ n , pc , 𝓁 ⟩ , pc ⟩
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ | nothing = error stuck
𝒱 γ (new 𝓁 `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | no _ = error NSUError

-- `new-dyn` is similar to `new` except that 𝓁 comes into play at runtime (instead of from typing derivation).
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label 𝓁) | just v with pc ≼? 𝓁
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label 𝓁) | just v | yes _ =
  let n = length μ in
    result ⟨ ⟨ n , pc , 𝓁 ⟩ ↦ ⟨ T , v ⟩ ∷ μ , V-ref ⟨ n , pc , 𝓁 ⟩ , pc ⟩
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label 𝓁) | just v | no _ =
  error NSUError
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | _ | _ = error stuck

𝒱 γ (eq-ref `x `y) (⊢eq-ref {x = x} {y} _ _ _ _) μ pc (suc k) with nth γ x | nth γ y
... | just (V-ref loc) | just (V-ref loc′) =
  result ⟨ μ , =?-ref loc loc′ , pc ⟩
  where
  =?-ref : (loc loc′ : Location) → Value
  =?-ref loc loc′ with loc ≟ₗ loc′
  ... | yes _ = V-true
  ... | no  _ = V-false
... | _ | _ = error stuck

-- Let binding
𝒱 {Γ} γ (`let M N) (⊢let {T = T} {T′} {S} {M} {N} ⊢M ⊢N T′≲T) μ pc (suc k) = do
  ⟨ μ′ , v′ , pc′ ⟩ ← 𝒱 {Γ} γ M ⊢M μ pc k
  ⟨ μ″ , v″ , pc″ ⟩ ← castT μ′ pc′ T′ T v′   -- need to cast T′ ⇛ T
  𝒱 {T ∷ Γ} (v″ ∷ γ) N ⊢N μ″ pc″ k

-- Lambda abstraction
𝒱 γ (ƛ N) (⊢ƛ ⊢N) μ pc (suc k) = result ⟨ μ , V-clos < N , γ , ⊢N > , pc ⟩

𝒱 γ (ref-label `x) (⊢ref-label {x = x} _) μ pc (suc k) with nth γ x
... | just (V-ref ⟨ n , 𝓁₁ , 𝓁₂ ⟩) = result ⟨ μ , V-label 𝓁₂ , pc ⟩ -- return 𝓁₂ since 𝓁₁ is the saved pc
... | _ = error stuck

𝒱 γ (lab-label `x) (⊢lab-label {x = x} _) μ pc (suc k) with nth γ x
... | just (V-lab 𝓁 v) = result ⟨ μ , V-label 𝓁 , pc ⟩
... | _ = error stuck

𝒱 γ pc-label ⊢pc-label μ pc (suc k) = result ⟨ μ , V-label pc , pc ⟩

𝒱 γ (`x `⊔ `y) (⊢⊔ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
... | just (V-label 𝓁x) | just (V-label 𝓁y) = result ⟨ μ , V-label (𝓁x ⊔ 𝓁y) , pc ⟩
... | _ | _ = error stuck

𝒱 γ (`x `⊓ `y) (⊢⊓ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
... | just (V-label 𝓁x) | just (V-label 𝓁y) = result ⟨ μ , V-label (𝓁x ⊓ 𝓁y) , pc ⟩
... | _ | _ = error stuck

𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) with 𝓁x ≼? 𝓁y
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) | yes _ =
  result ⟨ μ , V-true , pc ⟩
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label 𝓁x) | just (V-label 𝓁y) | no  _ =
  result ⟨ μ , V-false , pc ⟩
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | _ | _ = error stuck

𝒱 γ (unlabel `x) (⊢unlabel {x = x} _) μ pc (suc k) with nth γ x
... | just (V-lab 𝓁 v) = result ⟨ μ , v , pc ⊔ 𝓁 ⟩ -- need to update pc
... | _ = error stuck

𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) with 𝒱 γ M ⊢M μ pc k
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ with pc′ ≼? (pc ⊔ 𝓁)
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ | yes _ =
  result ⟨ μ′ , V-lab 𝓁 v , pc ⟩
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) | error err = error err
𝒱 γ (to-label 𝓁 M) (⊢to-label ⊢M _) μ pc (suc k) | timeout = timeout

-- Similar to `to-label` except that 𝓁 comes into play at runtime
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) with nth γ x
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) with 𝒱 γ M ⊢M μ pc k
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) | result ⟨ μ′ , v , pc′ ⟩ with pc′ ≼? (pc ⊔ 𝓁)
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) | result ⟨ μ′ , v , pc′ ⟩ | yes _ =
  result ⟨ μ′ , V-lab 𝓁 v , pc ⟩
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) | result ⟨ μ′ , v , pc′ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) | error err = error err
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label 𝓁) | timeout = timeout
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | _ = error stuck

-- Application
𝒱 γ (`x · `y) (⊢· {x = x} {y} {T} {T′} {S} {𝓁̂₁} {𝓁̂₁′} _ _ _ 𝓁̂₁′≾𝓁̂₁) μ pc (suc k)
    with nth γ x | nth γ y
... | just v | just w = do
    ⟨ μ′ , w′ , pc′ ⟩ ← castT μ pc T′ T w            -- cast T′ ⇛ T
    ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁  -- cast 𝓁̂₁′ ⇛ 𝓁̂₁
    apply γ v w′ μ pc k
... | _ | _ = error stuck

apply γ (V-clos < N , ρ , ⊢N >) w μ pc k = 𝒱 (w ∷ ρ) N ⊢N μ pc k
apply γ (V-proxy S T S′ T′ 𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S′≲S T≲T′ 𝓁̂₁′≾𝓁̂₁ 𝓁̂₂≾𝓁̂₂′ v) w μ pc k = do
    ⟨ μ₁ , w′ , pc₁ ⟩ ← castT μ pc S′ S w            -- cast S′ ⇛ S
    ⟨ μ₂ , _  , pc₂ ⟩ ← castL μ₁ pc₁ 𝓁̂₁′ 𝓁̂₁ 𝓁̂₁′≾𝓁̂₁  -- cast 𝓁̂₁′ ⇛ 𝓁̂₁
    ⟨ μ₃ , v₁ , pc₃ ⟩ ← apply γ v w′ μ₂ pc₂ k
    ⟨ μ₄ , _  , pc₄ ⟩ ← castL μ₃ pc₃ 𝓁̂₂ 𝓁̂₂′ 𝓁̂₂≾𝓁̂₂′  -- cast 𝓁̂₂ ⇛ 𝓁̂₂′
    castT μ₄ pc₄ T T′ v₁                              -- cast T ⇛ T′
apply γ _ w μ pc k = error stuck
