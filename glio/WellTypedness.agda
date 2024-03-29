module WellTypedness where


open import Data.Nat using (ℕ; zero; suc; _>_; _<_)
open import Data.Nat.Properties using (<⇒≢; <-trans; ≤-refl) renaming (_≟_ to _≟ₙ_)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym; cong; cong₂; subst; subst₂; trans)

open import Lemmas
open import StaticsGLIO
open import Store
open import Interp




infix 4 _∣_⊢ₑ_
infix 4 _⊢ᵥ_⦂_
infix 4 _⊢ₛ_


-- Well-typed environment γ under context Γ
data _∣_⊢ₑ_ : Context → Store → Env → Set
-- Well-typed value under store μ
--   NOTE: Since μ contains type information, it doubles as store typing context Σ here.
data _⊢ᵥ_⦂_ : Store → Value → 𝕋 → Set
-- Well-typed store
data _⊢ₛ_ : Store → Store → Set


data _∣_⊢ₑ_ where

  ⊢ₑ∅ : ∀ {μ}
      -------------
    → [] ∣ μ ⊢ₑ []

  ⊢ₑ∷ : ∀ {Γ μ γ v T}
    → μ ⊢ᵥ v ⦂ T
    → Γ ∣ μ ⊢ₑ γ
      -------------------
    → T ∷ Γ ∣ μ ⊢ₑ v ∷ γ


data _⊢ᵥ_⦂_ where

  ⊢ᵥtt : ∀ {μ}
      --------------- Unit
    → μ ⊢ᵥ V-tt ⦂ `⊤

  ⊢ᵥtrue : ∀ {μ}
      ------------------ True
    → μ ⊢ᵥ V-true ⦂ `𝔹

  ⊢ᵥfalse : ∀ {μ}
      ------------------- False
    → μ ⊢ᵥ V-false ⦂ `𝔹

  ⊢ᵥlabel : ∀ {μ ℓ}
      --------------------- Label
    → μ ⊢ᵥ V-label ℓ ⦂ `ℒ

  ⊢ᵥclos : ∀ {Δ μ γ T S M ℓ̂₁ ℓ̂₂}
    → Δ ∣ μ ⊢ₑ γ
    → (⊢M : T ∷ Δ [ ℓ̂₁ , ℓ̂₂ ]⊢ M ⦂ S)
      ------------------------------------------------ Closure
    → μ ⊢ᵥ V-clos < M , γ , ⊢M > ⦂ T [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S

  ⊢ᵥproxy : ∀ {μ S T S′ T′ v ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S′≲S T≲T′ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′}
    → μ ⊢ᵥ v ⦂ S [ ℓ̂₁ ]⇒[ ℓ̂₂ ] T
      ----------------------------------------------------------------------------------------- Proxy
    → μ ⊢ᵥ V-proxy S T S′ T′ ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S′≲S T≲T′ ℓ̂₁′≾ℓ̂₁ ℓ̂₂≾ℓ̂₂′ v ⦂ S′ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T′

  ⊢ᵥref : ∀ {μ T T′ n ℓ₁ ℓ₂ v}
    → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩  -- We only require that ⟨ n , ℓ₁ , ℓ₂ ⟩ is a valid address.
      ------------------------------------------- Ref
    → μ ⊢ᵥ V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩ ⦂ Ref (l̂ ℓ₂) T′

  ⊢ᵥref-dyn : ∀ {μ T T′ n ℓ₁ ℓ₂ v}
    → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩  -- We only require that ⟨ n , ℓ₁ , ℓ₂ ⟩ is a valid address.
      ------------------------------------------- RefDyn
    → μ ⊢ᵥ V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩ ⦂ Ref ¿ T′

  ⊢ᵥlab : ∀ {μ T v ℓ ℓ′}
    → ℓ ≼ ℓ′
    → μ ⊢ᵥ v ⦂ T
      ----------------------------- Labeled
    → μ ⊢ᵥ V-lab ℓ v ⦂ Lab (l̂ ℓ′) T

  ⊢ᵥlab-dyn : ∀ {μ T v ℓ}
    → μ ⊢ᵥ v ⦂ T
      -------------------------- LabeledDyn
    → μ ⊢ᵥ V-lab ℓ v ⦂ Lab ¿ T

data _⊢ₛ_ where

  ⊢ₛ∅ : ∀ {μ}
    → μ ⊢ₛ []

  ⊢ₛ∷ : ∀ {μ σ v T} {loc : Location}
    → μ ⊢ᵥ v ⦂ T
    → μ ⊢ₛ σ
      ----------------------------
    → μ ⊢ₛ (loc ↦ ⟨ T , v ⟩) ∷ σ


-- Well-typed result
infix 4 ⊢ᵣ_⦂_

data ⊢ᵣ_⦂_ : Result Conf → 𝕋 → Set where

  ⊢ᵣresult : ∀ {μ T v pc}
    → μ ⊢ₛ μ
    → μ ⊢ᵥ v ⦂ T
      ---------------------------------
    → ⊢ᵣ result ⟨ μ , v , pc ⟩ ⦂ T

  -- Cast error, NSU check failure and diverging are always well-typed under any T ∈ 𝕋
  --   NOTE: *stuck* is ruled out here !
  ⊢ᵣcast-error : ∀ {T}
    → ⊢ᵣ error castError ⦂ T

  ⊢ᵣnsu-error : ∀ {T}
    → ⊢ᵣ error NSUError ⦂ T

  ⊢ᵣtimeout : ∀ {T}
    → ⊢ᵣ timeout ⦂ T


result-≡-inv : ∀ {conf₁ conf₂ : Conf}
  → result conf₁ ≡ result conf₂
  → conf₁ ≡ conf₂
result-≡-inv refl = refl

-- Env lookup is safe
nth-safe : ∀ {Γ μ γ T v x}
  → Γ ∣ μ ⊢ₑ γ
  → nth Γ x ≡ just T
  → nth γ x ≡ just v
    ------------------
  → μ ⊢ᵥ v ⦂ T
nth-safe {μ = μ} {x = 0} (⊢ₑ∷ ⊢v₀ _) eq₁ eq₂ =
  let T₀≡T = just-≡-inv eq₁ in
  let v₀≡v = just-≡-inv eq₂ in
    subst₂ (λ □₁ □₂ → μ ⊢ᵥ □₁ ⦂ □₂) v₀≡v T₀≡T ⊢v₀
nth-safe {x = suc x} (⊢ₑ∷ _ Γμ⊢γ) eq₁ eq₂ = nth-safe Γμ⊢γ eq₁ eq₂

-- Heap lookup is safe
lookup-safe : ∀ {σ μ loc T v}
  → σ ⊢ₛ μ
  → lookup μ loc ≡ just ⟨ T , v ⟩
    ------------------------------
  → σ ⊢ᵥ v ⦂ T
lookup-safe ⊢ₛ∅ ()
lookup-safe {σ} { ⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ T₀ , v₀ ⟩ ∷ μ′ } {⟨ n , ℓ₁ , ℓ₂ ⟩} (⊢ₛ∷ ⊢v₀ ⊢μ′) eq
  with n₀ ≟ₙ n | ℓ₁₀ ≟ ℓ₁ | ℓ₂₀ ≟ ℓ₂
... | yes _ | yes _ | yes _ =
  let T₀v₀≡Tv = just-≡-inv eq in
  let eq′ = ×-≡-inv T₀v₀≡Tv in
  let T₀≡T = proj₁ eq′ in
  let v₀≡v = proj₂ eq′ in
  subst₂ (λ □₁ □₂ → σ ⊢ᵥ □₁ ⦂ □₂) v₀≡v T₀≡T ⊢v₀
... | yes _ | yes _ | no _  = lookup-safe ⊢μ′ eq
... | yes _ | no _ | yes _  = lookup-safe ⊢μ′ eq
... | no _ | yes _ | yes _  = lookup-safe ⊢μ′ eq
... | yes _ | no _ | no _  = lookup-safe ⊢μ′ eq
... | no _ | yes _ | no _  = lookup-safe ⊢μ′ eq
... | no _ | no _ | yes _  = lookup-safe ⊢μ′ eq
... | no _ | no _ | no _ = lookup-safe ⊢μ′ eq

-- If Σ ⊢ μ , ∀ loc ∈ Location , Σ ⊢ μ( loc ) ⦂ Σ( loc )
lookup-safe-corollary : ∀ {μ loc T v}
  → μ ⊢ₛ μ
  → lookup μ loc ≡ just ⟨ T , v ⟩
    ------------------------------
  → μ ⊢ᵥ v ⦂ T
lookup-safe-corollary {μ} ⊢μ eq = lookup-safe ⊢μ eq

⊢γ→∃v : ∀ {Γ μ γ x T}
  → Γ ∣ μ ⊢ₑ γ
  → nth Γ x ≡ just T
  → ∃[ v ] (nth γ x ≡ just v)
⊢γ→∃v {x = 0} (⊢ₑ∷ {v = v₀} ⊢v₀ ⊢γ) eq = ⟨ v₀ , refl ⟩
⊢γ→∃v {x = suc x} (⊢ₑ∷ {v = v₀} ⊢v₀ ⊢γ) eq = ⊢γ→∃v ⊢γ eq

⊢γ→⊢v : ∀ {Γ μ γ x T}
  → (⊢γ : Γ ∣ μ ⊢ₑ γ)
  → (eq : nth Γ x ≡ just T)
  → μ ⊢ᵥ proj₁ (⊢γ→∃v ⊢γ eq) ⦂ T
⊢γ→⊢v {x = 0} (⊢ₑ∷ {v = v₀} ⊢v₀ ⊢γ) eq rewrite sym (just-≡-inv eq) = ⊢v₀
⊢γ→⊢v {x = suc x} (⊢ₑ∷ {v = v₀} ⊢v₀ ⊢γ) eq = ⊢γ→⊢v ⊢γ eq

data _∉domₙ_ : ℕ → Store → Set where

  ∉domₙ∅ : ∀ {n} → n ∉domₙ []

  ∉domₙ∷ : ∀ {μ n n₀ ℓ₁₀ ℓ₂₀ T₀ v₀}
    → n₀ < n
    → n ∉domₙ μ
    → n ∉domₙ (⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ T₀ , v₀ ⟩ ∷ μ)

∉→lookup≡nothing : ∀ {μ n ℓ₁ ℓ₂}
  → n ∉domₙ μ
  → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ nothing
∉→lookup≡nothing {[]} ∉domₙ∅ = refl
∉→lookup≡nothing {⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ v₀ , T₀ ⟩ ∷ μ} {n} {ℓ₁} {ℓ₂} (∉domₙ∷ n₀<n n∉domμ)
  with ⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ≟ₗ ⟨ n , ℓ₁ , ℓ₂ ⟩
... | yes p≡ = let n₀≡n = proj₁ (×-≡-inv p≡) in ⊥-elim ((<⇒≢ n₀<n) n₀≡n)
... | no  _  = ∉→lookup≡nothing n∉domμ

lookup-≢ : ∀ {μ : Store} {n n′ ℓ₁ ℓ₂ T v}
  → lookup μ ⟨ n  , ℓ₁ , ℓ₂ ⟩ ≡ nothing
  → lookup μ ⟨ n′ , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
  → n ≢ n′
lookup-≢ {⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ T₀ , v₀ ⟩ ∷ μ} {n} {n′} {ℓ₁} {ℓ₂} {T} {v} lookup-n-nothing lookup-n′-something n≡n′ =
  let lookup-n-something = lookup-same {⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ T₀ , v₀ ⟩ ∷ μ} lookup-n′-something (sym n≡n′) in
  let nothing≡just = trans (sym lookup-n-nothing) lookup-n-something in
  nothing≢just nothing≡just
  where
  lookup-same : ∀ {μ}
    → lookup μ ⟨ n′ , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
    → n′ ≡ n
    → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
  lookup-same eq₁ eq₂ rewrite sym eq₂ = eq₁

ext-new-lookup-same : ∀ {μ n n₀ ℓ₁ ℓ₁₀ ℓ₂ ℓ₂₀ T T₀ v v₀}
  → n₀ ∉domₙ μ
  → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
  → lookup (⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ↦ ⟨ T₀ , v₀ ⟩ ∷ μ) ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
ext-new-lookup-same {μ} {n} {n₀} {ℓ₁} {ℓ₁₀} {ℓ₂} {ℓ₂₀} {T} {T₀} {v} {v₀} n₀∉domμ lookup-n-something
  with ⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ≟ₗ ⟨ n , ℓ₁ , ℓ₂ ⟩
... | yes p≡ =
  let lookup-n₀-nothing = ∉→lookup≡nothing {ℓ₁ = ℓ₁} {ℓ₂} n₀∉domμ in
  let n₀≢n = lookup-≢ {μ} {n₀} {n} {ℓ₁} {ℓ₂} {T} {v} lookup-n₀-nothing lookup-n-something in
  ⊥-elim (n₀≢n (proj₁ (×-≡-inv p≡)))
... | no  _ = lookup-n-something

ext-lookup-first : ∀ {μ : Store} {loc T v}
  → lookup (loc ↦ ⟨ T , v ⟩ ∷ μ) loc ≡ just ⟨ T , v ⟩
ext-lookup-first {loc = loc} rewrite proj₂ (≟ₗ-≡-normal {loc}) = refl

⊢castT′ : ∀ {μ pc T₁ T₂ v}
  → (T₁≲T₂ : T₁ ≲ T₂)
  → μ ⊢ₛ μ
  → μ ⊢ᵥ v ⦂ T₁
    ----------------------------------
  → ⊢ᵣ castT′ μ pc T₁ T₂ T₁≲T₂ v ⦂ T₂
⊢castT′ ≲-⊤ ⊢μ ⊢ᵥtt = ⊢ᵣresult ⊢μ ⊢ᵥtt

⊢castT′ ≲-𝔹 ⊢μ ⊢ᵥtrue = ⊢ᵣresult ⊢μ ⊢ᵥtrue
⊢castT′ ≲-𝔹 ⊢μ ⊢ᵥfalse = ⊢ᵣresult ⊢μ ⊢ᵥfalse

⊢castT′ ≲-ℒ ⊢μ ⊢ᵥlabel = ⊢ᵣresult ⊢μ ⊢ᵥlabel

⊢castT′ (≲-⇒ _ _ _ _) ⊢μ (⊢ᵥclos ⊢γ ⊢M) = ⊢ᵣresult ⊢μ (⊢ᵥproxy (⊢ᵥclos ⊢γ ⊢M))

⊢castT′ (≲-⇒ _ _ _ _) ⊢μ (⊢ᵥproxy ⊢v) = ⊢ᵣresult ⊢μ (⊢ᵥproxy (⊢ᵥproxy ⊢v))

⊢castT′ {T₁ = Ref ℓ̂₁ T₁} {Ref ℓ̂₂ T₂} {V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩} (≲-Ref _ _ _ _) ⊢μ (⊢ᵥref eq)
  with ℓ̂₂
... | ¿ = ⊢ᵣresult ⊢μ (⊢ᵥref-dyn eq)
... | (l̂ ℓ₂′)
  with ℓ₂ ≟ ℓ₂′
...   | yes ℓ₂≡ℓ₂′ rewrite (sym ℓ₂≡ℓ₂′) = ⊢ᵣresult ⊢μ (⊢ᵥref eq)
...   | no  _ = ⊢ᵣcast-error
⊢castT′ {T₁ = Ref ℓ̂₁ T₁} {Ref ℓ̂₂ T₂} {V-ref ⟨ n , ℓ₁ , ℓ₂ ⟩} (≲-Ref _ _ _ _) ⊢μ (⊢ᵥref-dyn eq)
  with ℓ̂₂
... | ¿ = ⊢ᵣresult ⊢μ (⊢ᵥref-dyn eq)
... | (l̂ ℓ₂′)
  with ℓ₂ ≟ ℓ₂′
...   | yes ℓ₂≡ℓ₂′ rewrite (sym ℓ₂≡ℓ₂′) = ⊢ᵣresult ⊢μ (⊢ᵥref eq)
...   | no  _ = ⊢ᵣcast-error

⊢castT′ {μ} {pc} {Lab (l̂ ℓ₁) T₁} {Lab (l̂ ℓ₂) T₂} {V-lab ℓ v} (≲-Lab (≾-l ℓ₁≼ℓ₂) T₁≲T₂) ⊢μ (⊢ᵥlab ℓ≼ℓ₁ ⊢v)
  with (l̂ ℓ) ≾? (l̂ ℓ₂)
... | no _ = ⊢ᵣcast-error
... | yes (≾-l ℓ≼ℓ₂)
  with castT′ μ pc T₁ T₂ T₁≲T₂ v | ⊢castT′ {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢μ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab ℓ≼ℓ₂ ⊢v′)
...   | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
⊢castT′ {μ} {pc} {Lab (l̂ ℓ₁) T₁} {Lab ¿ T₂} {V-lab ℓ v} (≲-Lab ≾-¿-r T₁≲T₂) ⊢μ (⊢ᵥlab ℓ≼ℓ₁ ⊢v)
  with castT′ μ pc T₁ T₂ T₁≲T₂ v | ⊢castT′ {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢μ ⊢v
... | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab-dyn ⊢v′)
... | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
... | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
... | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
⊢castT′ {μ} {pc} {Lab ¿ T₁} {Lab (l̂ ℓ₂) T₂} {V-lab ℓ v} (≲-Lab _ T₁≲T₂) ⊢μ (⊢ᵥlab-dyn ⊢v)
  with (l̂ ℓ) ≾? (l̂ ℓ₂)
... | no _ = ⊢ᵣcast-error
... | yes (≾-l ℓ≼ℓ₂)
  with castT′ μ pc T₁ T₂ T₁≲T₂ v | ⊢castT′ {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢μ ⊢v
...   | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab ℓ≼ℓ₂ ⊢v′)
...   | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
...   | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
...   | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error
⊢castT′ {μ} {pc} {Lab ¿ T₁} {Lab ¿ T₂} {V-lab ℓ v} (≲-Lab _ T₁≲T₂) ⊢μ (⊢ᵥlab-dyn ⊢v)
  with castT′ μ pc T₁ T₂ T₁≲T₂ v | ⊢castT′ {μ} {pc} {T₁} {T₂} {v} T₁≲T₂ ⊢μ ⊢v
... | result ⟨ μ′ , v′ , pc′ ⟩ | ⊢ᵣresult ⊢μ′ ⊢v′ = ⊢ᵣresult ⊢μ′ (⊢ᵥlab-dyn ⊢v′)
... | timeout | ⊢ᵣtimeout = ⊢ᵣtimeout
... | error NSUError | ⊢ᵣnsu-error = ⊢ᵣnsu-error
... | error castError | ⊢ᵣcast-error = ⊢ᵣcast-error

⊢castT : ∀ {μ pc T₁ T₂ v}
  → μ ⊢ₛ μ
  → μ ⊢ᵥ v ⦂ T₁
    ----------------------------
  → ⊢ᵣ castT μ pc T₁ T₂ v ⦂ T₂
⊢castT {T₁ = T₁} {T₂} ⊢μ ⊢v
  with T₁ ≲? T₂
... | yes T₁≲T₂ = ⊢castT′ T₁≲T₂ ⊢μ ⊢v
... | no  _ = ⊢ᵣcast-error


⊢castL : ∀ {μ pc ℓ̂₁ ℓ̂₂}
  → (ℓ̂₁≾ℓ̂₂ : ℓ̂₁ ≾ ℓ̂₂)
  → μ ⊢ₛ μ
  → ⊢ᵣ castL μ pc ℓ̂₁ ℓ̂₂ ℓ̂₁≾ℓ̂₂ ⦂ `⊤
⊢castL {μ} {pc} {ℓ̂₁} {ℓ̂₂} ℓ̂₁≾ℓ̂₂ ⊢μ with (l̂ pc) ≾? ℓ̂₂
... | yes _ = ⊢ᵣresult ⊢μ ⊢ᵥtt
... | no  _ = ⊢ᵣcast-error

ext-update-pres-⊢ᵥ : ∀ {μ loc T Tᵥ w w′ v}
  → lookup μ loc ≡ just ⟨ T , w ⟩
  → μ ⊢ᵥ w′ ⦂ T
  → μ ⊢ᵥ v ⦂ Tᵥ
    --------------------------------
  → loc ↦ ⟨ T , w′ ⟩ ∷ μ ⊢ᵥ v ⦂ Tᵥ

ext-update-pres-⊢ₛ : ∀ {μ σ loc T w w′}
  → μ ⊢ₛ σ
  → lookup μ loc ≡ just ⟨ T , w ⟩
  → μ ⊢ᵥ w′ ⦂ T
    -------------------------------
  → loc ↦ ⟨ T , w′ ⟩ ∷ μ ⊢ₛ σ

ext-update-pres-⊢ₑ : ∀ {Γ μ γ loc T w w′}
  → lookup μ loc ≡ just ⟨ T , w ⟩
  → Γ ∣ μ ⊢ₑ γ
  → μ ⊢ᵥ w′ ⦂ T
    --------------------------------
  → Γ ∣ loc ↦ ⟨ T , w′ ⟩ ∷ μ ⊢ₑ γ

ext-update-pres-⊢ₑ eq ⊢ₑ∅ ⊢w′ = ⊢ₑ∅
ext-update-pres-⊢ₑ eq (⊢ₑ∷ ⊢v ⊢γ) ⊢w′ =
  ⊢ₑ∷ (ext-update-pres-⊢ᵥ eq ⊢w′ ⊢v) (ext-update-pres-⊢ₑ eq ⊢γ ⊢w′)

ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢ᵥtt = ⊢ᵥtt
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢ᵥtrue = ⊢ᵥtrue
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢ᵥfalse = ⊢ᵥfalse
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢ᵥlabel = ⊢ᵥlabel
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ (⊢ᵥclos ⊢γ ⊢M) = ⊢ᵥclos (ext-update-pres-⊢ₑ eq ⊢γ ⊢ᵥw′) ⊢M
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ (⊢ᵥproxy ⊢v) = ⊢ᵥproxy (ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢v)
ext-update-pres-⊢ᵥ {μ} {loc} {T} {w = w} {w′} {V-ref loc′} eq ⊢ᵥw′ (⊢ᵥref {T = Tᵥ} {v = v} eq′)
  with loc ≟ₗ loc′
... | yes loc≡loc′ = ⊢ᵥref hit
  where
  hit : lookup (loc ↦ ⟨ T , w′ ⟩ ∷ μ) loc′ ≡ just ⟨ T , w′ ⟩
  hit rewrite loc≡loc′ | proj₂ (≟ₗ-≡-normal {loc′}) = refl
... | no  loc≢loc′ = ⊢ᵥref hit
  where
  hit : lookup (loc ↦ ⟨ T , w′ ⟩ ∷ μ) loc′ ≡ just ⟨ Tᵥ , v ⟩
  hit rewrite proj₂ (≟ₗ-≢-normal loc≢loc′) = eq′
ext-update-pres-⊢ᵥ {μ} {loc} {T} {w = w} {w′} {V-ref loc′} eq ⊢ᵥw′ (⊢ᵥref-dyn {T = Tᵥ} {v = v} eq′)
  with loc ≟ₗ loc′
... | yes loc≡loc′ = ⊢ᵥref-dyn hit
  where
  hit : lookup (loc ↦ ⟨ T , w′ ⟩ ∷ μ) loc′ ≡ just ⟨ T , w′ ⟩
  hit rewrite loc≡loc′ | proj₂ (≟ₗ-≡-normal {loc′}) = refl
... | no  loc≢loc′ = ⊢ᵥref-dyn hit
  where
  hit : lookup (loc ↦ ⟨ T , w′ ⟩ ∷ μ) loc′ ≡ just ⟨ Tᵥ , v ⟩
  hit rewrite proj₂ (≟ₗ-≢-normal loc≢loc′) = eq′
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ (⊢ᵥlab ℓ≼ℓ′ ⊢v) = ⊢ᵥlab ℓ≼ℓ′ (ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢v)
ext-update-pres-⊢ᵥ eq ⊢ᵥw′ (⊢ᵥlab-dyn ⊢v)  = ⊢ᵥlab-dyn  (ext-update-pres-⊢ᵥ eq ⊢ᵥw′ ⊢v)

ext-update-pres-⊢ₛ ⊢ₛ∅ eq ⊢w′ = ⊢ₛ∅
ext-update-pres-⊢ₛ {μ} {σ} {loc} {T} {w} {w′} (⊢ₛ∷ ⊢v ⊢σ) eq ⊢w′ =
  ⊢ₛ∷ (ext-update-pres-⊢ᵥ eq ⊢w′ ⊢v) (ext-update-pres-⊢ₛ ⊢σ eq ⊢w′)

ext-new-pres-⊢ₑ : ∀ {Γ μ γ n ℓ₁ ℓ₂ T w}
  → n ∉domₙ μ
  → Γ ∣ μ ⊢ₑ γ
  → μ ⊢ᵥ w ⦂ T
    --------------------------------
  → Γ ∣ ⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , w ⟩ ∷ μ ⊢ₑ γ

ext-new-pres-⊢ᵥ : ∀ {μ n ℓ₁ ℓ₂ T Tᵥ w v}
  → n ∉domₙ μ
  → μ ⊢ᵥ w ⦂ T
  → μ ⊢ᵥ v ⦂ Tᵥ
    --------------------------------
  → ⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , w ⟩ ∷ μ ⊢ᵥ v ⦂ Tᵥ

ext-new-pres-⊢ₛ : ∀ {μ σ n ℓ₁ ℓ₂ T v}
  → μ ⊢ₛ σ
  → n ∉domₙ μ
  → μ ⊢ᵥ v ⦂ T
    -------------------------------
  → ⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , v ⟩ ∷ μ ⊢ₛ σ

ext-new-pres-⊢ₑ fresh ⊢ₑ∅ ⊢w = ⊢ₑ∅
ext-new-pres-⊢ₑ fresh (⊢ₑ∷ ⊢v ⊢γ) ⊢w =
  ⊢ₑ∷ (ext-new-pres-⊢ᵥ fresh ⊢w ⊢v) (ext-new-pres-⊢ₑ fresh ⊢γ ⊢w)

ext-new-pres-⊢ᵥ fresh ⊢w ⊢ᵥtt = ⊢ᵥtt
ext-new-pres-⊢ᵥ fresh ⊢w ⊢ᵥtrue = ⊢ᵥtrue
ext-new-pres-⊢ᵥ fresh ⊢w ⊢ᵥfalse = ⊢ᵥfalse
ext-new-pres-⊢ᵥ fresh ⊢w ⊢ᵥlabel = ⊢ᵥlabel
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥclos ⊢γ ⊢M) = ⊢ᵥclos (ext-new-pres-⊢ₑ fresh ⊢γ ⊢w) ⊢M
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥproxy ⊢v) = ⊢ᵥproxy (ext-new-pres-⊢ᵥ fresh ⊢w ⊢v)
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥref eq) = ⊢ᵥref (ext-new-lookup-same fresh eq)
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥref-dyn eq) = ⊢ᵥref-dyn (ext-new-lookup-same fresh eq)
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥlab ℓ≼ℓ′ ⊢v) = ⊢ᵥlab ℓ≼ℓ′ (ext-new-pres-⊢ᵥ fresh ⊢w ⊢v)
ext-new-pres-⊢ᵥ fresh ⊢w (⊢ᵥlab-dyn tv) = ⊢ᵥlab-dyn (ext-new-pres-⊢ᵥ fresh ⊢w tv)

ext-new-pres-⊢ₛ ⊢ₛ∅ fresh ⊢v = ⊢ₛ∅
ext-new-pres-⊢ₛ (⊢ₛ∷ {v = v₀} {T = T₀} ⊢v₀ ⊢σ) fresh ⊢v =
  ⊢ₛ∷ (ext-new-pres-⊢ᵥ fresh ⊢v ⊢v₀) (ext-new-pres-⊢ₛ ⊢σ fresh ⊢v)

private
  n<1+n : ∀ n → n < suc n
  n<1+n 0 = Data.Nat.s≤s Data.Nat.z≤n
  n<1+n (suc n) = Data.Nat.s≤s (n<1+n n)

  fresh-weaken : ∀ {μ n}
    → n ∉domₙ μ
    → (suc n) ∉domₙ μ
  fresh-weaken ∉domₙ∅ = ∉domₙ∅
  fresh-weaken {μ} {n} (∉domₙ∷ n₀<n fresh) = ∉domₙ∷ (<-trans n₀<n (n<1+n n)) (fresh-weaken fresh)

  n<lengthμ : ∀ {μ : Store} {n m ℓ₁ ℓ₂ T v}
    → m ∉domₙ μ
    → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
    → n < m
  n<lengthμ {n = n} {m} {ℓ₁} {ℓ₂} (∉domₙ∷ {μ} {m} {n₀} {ℓ₁₀} {ℓ₂₀} n₀<m fresh) eq
    with ⟨ n₀ , ℓ₁₀ , ℓ₂₀ ⟩ ≟ₗ ⟨ n , ℓ₁ , ℓ₂ ⟩
  ... | yes p≡ rewrite sym (proj₁ (×-≡-inv p≡)) = n₀<m
  ... | no ¬p≡ = n<lengthμ fresh eq


ext-new-fresh : ∀ {μ n ℓ₁ ℓ₂ T v}
  → length μ ∉domₙ μ
  → n ≡ length μ
  → length (⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , v ⟩ ∷ μ) ∉domₙ (⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , v ⟩ ∷ μ)
ext-new-fresh {μ} fresh eq rewrite eq = ∉domₙ∷ (n<1+n (length μ)) (fresh-weaken fresh)

ext-update-fresh : ∀ {μ n ℓ₁ ℓ₂ T v w}
  → length μ ∉domₙ μ
  → lookup μ ⟨ n , ℓ₁ , ℓ₂ ⟩ ≡ just ⟨ T , v ⟩
  → length (⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , w ⟩ ∷ μ) ∉domₙ (⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , w ⟩ ∷ μ)
ext-update-fresh {μ} {n} {ℓ₁} {ℓ₂} {T} {v} fresh eq = ∉domₙ∷ (<-trans n<lenμ lenμ<lenv∷μ) (fresh-weaken fresh)
  where
  n<lenμ : n < length μ
  n<lenμ = n<lengthμ fresh eq
  lenμ<lenv∷μ : length μ < length ((⟨ n , ℓ₁ , ℓ₂ ⟩ ↦ ⟨ T , v ⟩) ∷ μ)
  lenμ<lenv∷μ = Data.Nat.s≤s ≤-refl

⊢ₑ→nth⊢ᵥ : ∀ {Γ μ γ x v T}
  → Γ ∣ μ ⊢ₑ γ
  → nth γ x ≡ just v
  → nth Γ x ≡ just T
  → μ ⊢ᵥ v ⦂ T
⊢ₑ→nth⊢ᵥ {x = zero} (⊢ₑ∷ ⊢v₀ ⊢γ) γ[x]≡v Γ[x]≡T =
  let v₀≡v = just-≡-inv γ[x]≡v in
  let T₀≡T = just-≡-inv Γ[x]≡T in
    subst₂ (λ □₁ □₂ → _ ⊢ᵥ □₁ ⦂ □₂) v₀≡v T₀≡T ⊢v₀
⊢ₑ→nth⊢ᵥ {x = suc x} (⊢ₑ∷ ⊢v₀ ⊢γ) γ[x]≡v Γ[x]≡T = ⊢ₑ→nth⊢ᵥ ⊢γ γ[x]≡v Γ[x]≡T
