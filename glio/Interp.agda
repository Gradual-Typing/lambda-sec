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


-- Cast ℓ̂₁ ⇛ ℓ̂₂
--   This can only happen where ℓ̂₁ ≾ ℓ̂₂
castL : (μ : Store) → (pc : ℒ) → (ℓ̂₁ ℓ̂₂ : ℒ̂) → ℓ̂₁ ≾ ℓ̂₂ → Result Conf
castL μ pc ℓ̂₁ ℓ̂₂ ℓ̂₁≾ℓ̂₂ with (l̂ pc) ≾? ℓ̂₂
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
castT′ μ pc `ℒ `ℒ ≲-ℒ (V-label ℓ) = result ⟨ μ , V-label ℓ , pc ⟩
castT′ μ pc `ℒ `ℒ ≲-ℒ _            = error stuck
-- Ref ⇛ Ref
castT′ μ pc (Ref ℓ̂₁ T₁′) (Ref ℓ̂₂ T₂′) (≲-Ref _ _ _ _) (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) with ℓ̂₂
... | ¿ = result ⟨ μ , V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩ , pc ⟩
... | (l̂ ℓ₂′) with ℓ₂ ≟ ℓ₂′
...   | no _ = error castError
...   | yes _ = result ⟨ μ , V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩ , pc ⟩
castT′ μ pc (Ref ℓ₁ T₁′) (Ref ℓ₂ T₂′) (≲-Ref _ _ _ _) _ = error stuck
-- Labeled ⇛ Labeled
castT′ μ pc (Lab ℓ̂₁ T₁′) (Lab ℓ̂₂ T₂′) (≲-Lab _ T₁′≲T₂′) (V-lab ℓ v) with (l̂ ℓ) ≾? ℓ̂₂
... | no _ = error castError
... | yes _ =
  do
  ⟨ μ′ , v′ , pc′ ⟩ ← castT′ μ pc T₁′ T₂′ T₁′≲T₂′ v
  result ⟨ μ′ , V-lab ℓ v′ , pc′ ⟩
castT′ μ pc (Lab ℓ̂₁ T₁′) (Lab ℓ̂₂ T₂′) (≲-Lab _ _) _ = error stuck
-- Closure ⇛ Proxied closure
--   NOTE: We need to build proxy here.
castT′ μ pc (S [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T) (S′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T′) (≲-⇒ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′ S′≲S T≲T′) v with v
... | (V-clos _) =
      result ⟨ μ , V-proxy S T S′ T′ ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S′≲S T≲T′  ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′ v , pc ⟩
... | (V-proxy _ _ _ _ _ _ _ _ _ _ _ _ _) =
      result ⟨ μ , V-proxy S T S′ T′ ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S′≲S T≲T′ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′  v , pc ⟩
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
𝒱 : ∀ {Γ T ℓ̂₁ ℓ̂₂} → (γ : Env) → (M : Term) → Γ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ T → (μ : Store) → (pc : ℒ) → (k : ℕ) → Result Conf
apply : Env → Value → Value → Store → (pc : ℒ) → (k : ℕ) → Result Conf

-- Running out of gas
𝒱 _ _ _ _ _ 0 = timeout

𝒱 γ `tt _       μ pc (suc k) = result ⟨ μ , V-tt , pc ⟩
𝒱 γ `true _     μ pc (suc k) = result ⟨ μ , V-true , pc ⟩
𝒱 γ `false _    μ pc (suc k) = result ⟨ μ , V-false , pc ⟩
𝒱 γ (label ℓ) _ μ pc (suc k) = result ⟨ μ , V-label ℓ , pc ⟩

𝒱 γ (` x) _ μ pc (suc k) with nth γ x
... | nothing = error stuck
... | just v = result ⟨ μ , v , pc ⟩

𝒱 γ (if `x M N) (⊢if {x = x} {T} {T′} {T″} {M} {N} {ℓ̂₁} {ℓ̂₂} {ℓ̂₂′} _ ⊢M ⊢N _) μ pc (suc k) with nth γ x
--   : goes to the M branch
... | just V-true = do
  ⟨ μ′ , vₘ , pc′ ⟩ ← 𝒱 γ M ⊢M μ pc k
  ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ ℓ̂₂ (ℓ̂₂ ⋎ ℓ̂₂′) (ℓ̂≾ℓ̂⋎ℓ̂′ _ _)
  castT μ″ pc″ T T″ vₘ  -- cast T ⇛ T″ , where T ∨ T′ ≡ T″
--   : goes to the N branch
... | just V-false = do
  ⟨ μ′ , vₙ , pc′ ⟩ ← 𝒱 γ N ⊢N μ pc k
  ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ ℓ̂₂′ (ℓ̂₂ ⋎ ℓ̂₂′) (ℓ̂≾ℓ̂′⋎ℓ̂ _ _)
  castT μ″ pc″ T′ T″ vₙ -- cast T′ ⇛ T″ , where T ∨ T′ ≡ T″
... | _ = error stuck

𝒱 γ (get `x) (⊢get {x = x} {T} {ℓ̂₁} {ℓ̂} _) μ pc (suc k) with nth γ x
𝒱 γ (get `x) (⊢get {x = x} {T} {ℓ̂₁} {ℓ̂} _) μ pc (suc k) | just (V-ref loc) with lookup μ loc
𝒱 γ (get `x) (⊢get {x = x} {T} {ℓ̂₁} {ℓ̂} _) μ pc (suc k) | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) | just ⟨ T′ , v ⟩ =
  castT μ (pc ⊔ ℓ₂) T′ T v  -- need to update pc
𝒱 γ (get `x) (⊢get {x = x} {T} {ℓ̂₁} {ℓ̂} _) μ pc (suc k) | just (V-ref loc) | nothing =
  -- error memAccError
  error stuck
𝒱 γ (get `x) (⊢get {x = x} {T} {ℓ̂₁} {ℓ̂} _) μ pc (suc k) | _ = error stuck

𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {ℓ̂₁} _ _ T′≲T _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {ℓ̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref loc) | just v with lookup μ loc
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {ℓ̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) | just v | just ⟨ T″ , _ ⟩ =
  do
  {- NOTE:
    We do not taint pc here like we do in `get`'s case, since the value is discarded and the
    type tag T″ is not used anywhere afterwards in the evaluation - the `set` clause always
    returns unit, which never leaks information.
  -}
  ⟨ μ′ , v′ , pc′ ⟩ ← castT μ  pc T′ T v
  ⟨ μ″ , v″ , pc″ ⟩ ← castT μ′ pc′ T T″ v′
  setmem μ″ ⟨ n , ℓ₁ , ℓ₂ ⟩ pc″ ⟨ T″ , v″ ⟩
  where
  setmem : (μ : Store) → (loc : Location) → (pc : ℒ) → 𝕋 × Value → Result Conf
  setmem μ ⟨ n , ℓ₁ , ℓ₂ ⟩ pc Tv with pc ≼? ℓ₂
  ... | yes _ = result ⟨ ⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ Tv ∷ μ , V-tt , pc ⟩
  ... | no _ = error NSUError
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {ℓ̂₁} _ _ T′≲T _) μ pc (suc k) | just (V-ref loc) | just v | nothing =
  -- error memAccError
  error stuck
𝒱 γ (set `x `y) (⊢set {x = x} {y} {T} {T′} {ℓ̂₁} _ _ T′≲T _) μ pc (suc k) | _ | _ = error stuck

𝒱 γ (new ℓ `y) (⊢new {y = y} {T} eq _) μ pc (suc k) with pc ≼? ℓ
𝒱 γ (new ℓ `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ with nth γ y
𝒱 γ (new ℓ `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ | just v =
  let n = length μ in
    result ⟨ ⟨ n , pc , ℓ ⟩ ↦ ⟨ T , v ⟩ ∷ μ , V-ref ⟨ n , pc , ℓ ⟩ , pc ⟩
𝒱 γ (new ℓ `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | yes _ | nothing = error stuck
𝒱 γ (new ℓ `y) (⊢new {y = y} {T} eq _) μ pc (suc k) | no _ = error NSUError

-- `new-dyn` is similar to `new` except that ℓ comes into play at runtime (instead of from typing derivation).
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label ℓ) | just v with pc ≼? ℓ
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label ℓ) | just v | yes _ =
  let n = length μ in
    result ⟨ ⟨ n , pc , ℓ ⟩ ↦ ⟨ T , v ⟩ ∷ μ , V-ref ⟨ n , pc , ℓ ⟩ , pc ⟩
𝒱 γ (new-dyn `x `y) (⊢new-dyn {x = x} {y} {T} _ _) μ pc (suc k) | just (V-label ℓ) | just v | no _ =
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
... | just (V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩) = result ⟨ μ , V-label ℓ₂ , pc ⟩ -- return ℓ₂ since ℓ₁ is the saved pc
... | _ = error stuck

𝒱 γ (lab-label `x) (⊢lab-label {x = x} _) μ pc (suc k) with nth γ x
... | just (V-lab ℓ v) = result ⟨ μ , V-label ℓ , pc ⟩
... | _ = error stuck

𝒱 γ pc-label ⊢pc-label μ pc (suc k) = result ⟨ μ , V-label pc , pc ⟩

𝒱 γ (`x `⊔ `y) (⊢⊔ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
... | just (V-label ℓx) | just (V-label ℓy) = result ⟨ μ , V-label (ℓx ⊔ ℓy) , pc ⟩
... | _ | _ = error stuck

𝒱 γ (`x `⊓ `y) (⊢⊓ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
... | just (V-label ℓx) | just (V-label ℓy) = result ⟨ μ , V-label (ℓx ⊓ ℓy) , pc ⟩
... | _ | _ = error stuck

𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) with nth γ x | nth γ y
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label ℓx) | just (V-label ℓy) with ℓx ≼? ℓy
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label ℓx) | just (V-label ℓy) | yes _ =
  result ⟨ μ , V-true , pc ⟩
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | just (V-label ℓx) | just (V-label ℓy) | no  _ =
  result ⟨ μ , V-false , pc ⟩
𝒱 γ (`x `≼ `y) (⊢≼ {x = x} {y} _ _) μ pc (suc k) | _ | _ = error stuck

𝒱 γ (unlabel `x) (⊢unlabel {x = x} _) μ pc (suc k) with nth γ x
... | just (V-lab ℓ v) = result ⟨ μ , v , pc ⊔ ℓ ⟩ -- need to update pc
... | _ = error stuck

𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) with 𝒱 γ M ⊢M μ pc k
𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ with pc′ ≼? (pc ⊔ ℓ)
𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ | yes _ =
  result ⟨ μ′ , V-lab ℓ v , pc ⟩
𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) | result ⟨ μ′ , v , pc′ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) | error err = error err
𝒱 γ (to-label ℓ M) (⊢to-label ⊢M _) μ pc (suc k) | timeout = timeout

-- Similar to `to-label` except that ℓ comes into play at runtime
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) with nth γ x
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) with 𝒱 γ M ⊢M μ pc k
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) | result ⟨ μ′ , v , pc′ ⟩ with pc′ ≼? (pc ⊔ ℓ)
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) | result ⟨ μ′ , v , pc′ ⟩ | yes _ =
  result ⟨ μ′ , V-lab ℓ v , pc ⟩
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) | result ⟨ μ′ , v , pc′ ⟩ | no  _ =
  error NSUError
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) | error err = error err
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | just (V-label ℓ) | timeout = timeout
𝒱 γ (to-label-dyn `x M) (⊢to-label-dyn {x = x} _ ⊢M) μ pc (suc k) | _ = error stuck

-- Application
𝒱 γ (`x · `y) (⊢· {x = x} {y} {T} {T′} {S} {ℓ̂₁} {ℓ̂₁′} _ _ _ ℓ̂₁′≾ℓ̂₁) μ pc (suc k)
    with nth γ x | nth γ y
... | just v | just w = do
    ⟨ μ′ , w′ , pc′ ⟩ ← castT μ pc T′ T w            -- cast T′ ⇛ T
    ⟨ μ″ , _  , pc″ ⟩ ← castL μ′ pc′ ℓ̂₁′ ℓ̂₁ ℓ̂₁′≾ℓ̂₁  -- cast ℓ̂₁′ ⇛ ℓ̂₁
    apply γ v w′ μ pc k
... | _ | _ = error stuck

apply γ (V-clos < N , ρ , ⊢N >) w μ pc k = 𝒱 (w ∷ ρ) N ⊢N μ pc k
apply γ (V-proxy S T S′ T′ ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S′≲S T≲T′ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′ v) w μ pc k = do
    ⟨ μ₁ , w′ , pc₁ ⟩ ← castT μ pc S′ S w            -- cast S′ ⇛ S
    ⟨ μ₂ , _  , pc₂ ⟩ ← castL μ₁ pc₁ ℓ̂₁′ ℓ̂₁ ℓ̂₁′≾ℓ̂₁  -- cast ℓ̂₁′ ⇛ ℓ̂₁
    ⟨ μ₃ , v₁ , pc₃ ⟩ ← apply γ v w′ μ₂ pc₂ k
    ⟨ μ₄ , _  , pc₄ ⟩ ← castL μ₃ pc₃ ℓ̂₂ ℓ̂₂′ ℓ̂₂≾ℓ̂₂′  -- cast ℓ̂₂ ⇛ ℓ̂₂′
    castT μ₄ pc₄ T T′ v₁                              -- cast T ⇛ T′
apply γ _ w μ pc k = error stuck
