module Consistency where

open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl; sym)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Data.Empty using (⊥; ⊥-elim)

open import StaticsGLIO
open import Lemmas using (≼-refl; ≼-antisym)
open import Iff using (_⇔_)



-- Consistency for labels
infixl 9 _~_

data _~_ : ℒ̂ → ℒ̂ → Set where

  ~-¿-r : ∀ {ℓ̂} → ℓ̂ ~ ¿

  ~-¿-l : ∀ {ℓ̂} → ¿ ~ ℓ̂

  ~-l : ∀ {ℓ} → (l̂ ℓ) ~ (l̂ ℓ)

-- Consistency for types
infixl 9 _∼_

data _∼_ : 𝕋 → 𝕋 → Set where

  ∼-⊤ : `⊤ ∼ `⊤

  ∼-𝔹 : `𝔹 ∼ `𝔹

  ∼-ℒ : `ℒ ∼ `ℒ

  ∼-Ref : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ~ ℓ̂₂
    → T₁ ∼ T₂
      ----------------------
    → Ref ℓ̂₁ T₁ ∼ Ref ℓ̂₂ T₂

  ∼-Lab : ∀ {ℓ̂₁ ℓ̂₂ T₁ T₂}
    → ℓ̂₁ ~ ℓ̂₂
    → T₁ ∼ T₂
      ----------------------
    → Lab ℓ̂₁ T₁ ∼ Lab ℓ̂₂ T₂

  ∼-⇒ : ∀ {ℓ̂₁ ℓ̂₂ ℓ̂₁′ ℓ̂₂′ S₁ S₂ T₁ T₂}
    → ℓ̂₁ ~ ℓ̂₁′
    → ℓ̂₂ ~ ℓ̂₂′
    → S₁ ∼ T₁
    → S₂ ∼ T₂
      ---------------------------------------------------
    → (S₁ [ ℓ̂₁ ]⇒[ ℓ̂₂ ] S₂) ∼ (T₁ [ ℓ̂₁′ ]⇒[ ℓ̂₂′ ] T₂)

ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ : ∀ ℓ̂ ℓ̂′ → (ℓ̂ ~ ℓ̂′) ⇔ (ℓ̂ ≾ ℓ̂′ × ℓ̂′ ≾ ℓ̂)
ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ ℓ̂ ℓ̂′ = record { to = to ; from = from }
  where
  to : ℓ̂ ~ ℓ̂′ → ℓ̂ ≾ ℓ̂′ × ℓ̂′ ≾ ℓ̂
  to ~-¿-r = ⟨ ≾-¿-r , ≾-¿-l ⟩
  to ~-¿-l = ⟨ ≾-¿-l , ≾-¿-r ⟩
  to ~-l = ⟨ ≾-l (≼-refl _) , ≾-l (≼-refl _) ⟩

  from : ℓ̂ ≾ ℓ̂′ × ℓ̂′ ≾ ℓ̂ → ℓ̂ ~ ℓ̂′
  from ⟨ ≾-¿-r , _ ⟩ = ~-¿-r
  from ⟨ ≾-¿-l , _ ⟩ = ~-¿-l
  from ⟨ ≾-l ℓ≼ℓ′ , ≾-l ℓ′≼ℓ ⟩ rewrite ≼-antisym ℓ≼ℓ′ ℓ′≼ℓ = ~-l

S∼T⇔S≲T×T≲S : ∀ S T → (S ∼ T) ⇔ (S ≲ T × T ≲ S)
S∼T⇔S≲T×T≲S S T = record { to = to ; from = from }
  where
  to : S ∼ T → S ≲ T × T ≲ S
  to ∼-⊤ = ⟨ ≲-⊤ , ≲-⊤ ⟩
  to ∼-𝔹 = ⟨ ≲-𝔹 , ≲-𝔹 ⟩
  to ∼-ℒ = ⟨ ≲-ℒ , ≲-ℒ ⟩
  to (∼-Ref ℓ₁~ℓ₂ S∼T) =
    let ⟨ ℓ₁≾ℓ₂ , ℓ₂≾ℓ₁ ⟩ = _⇔_.to (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ℓ₁~ℓ₂ in
    let ⟨ T₁≲T₂ , T₂≲T₁ ⟩ = _⇔_.to (S∼T⇔S≲T×T≲S _ _) S∼T in
      ⟨ ≲-Ref ℓ₁≾ℓ₂ ℓ₂≾ℓ₁ T₁≲T₂ T₂≲T₁ , ≲-Ref ℓ₂≾ℓ₁ ℓ₁≾ℓ₂ T₂≲T₁ T₁≲T₂ ⟩
  to (∼-Lab ℓ₁~ℓ₂ S∼T) =
    let ⟨ ℓ₁≾ℓ₂ , ℓ₂≾ℓ₁ ⟩ = _⇔_.to (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ℓ₁~ℓ₂ in
    let ⟨ T₁≲T₂ , T₂≲T₁ ⟩ = _⇔_.to (S∼T⇔S≲T×T≲S _ _) S∼T in
      ⟨ ≲-Lab ℓ₁≾ℓ₂ T₁≲T₂ , ≲-Lab ℓ₂≾ℓ₁ T₂≲T₁ ⟩
  to (∼-⇒ ℓ₁~ℓ₁′ ℓ₂~ℓ₂′ S₁∼T₁ S₂∼T₂) =
    let ⟨ ℓ₁≾ℓ₁′ , ℓ₁′≾ℓ₁ ⟩ = _⇔_.to (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ℓ₁~ℓ₁′ in
    let ⟨ ℓ₂≾ℓ₂′ , ℓ₂′≾ℓ₂ ⟩ = _⇔_.to (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ℓ₂~ℓ₂′ in
    let ⟨ S₁≲T₁ , T₁≲S₁ ⟩ = _⇔_.to (S∼T⇔S≲T×T≲S _ _) S₁∼T₁ in
    let ⟨ S₂≲T₂ , T₂≲S₂ ⟩ = _⇔_.to (S∼T⇔S≲T×T≲S _ _) S₂∼T₂ in
      ⟨ ≲-⇒ ℓ₁′≾ℓ₁ ℓ₂≾ℓ₂′ T₁≲S₁ S₂≲T₂ , ≲-⇒ ℓ₁≾ℓ₁′ ℓ₂′≾ℓ₂ S₁≲T₁ T₂≲S₂ ⟩

  from : S ≲ T × T ≲ S → S ∼ T
  from ⟨ ≲-⊤ , ≲-⊤ ⟩ = ∼-⊤
  from ⟨ ≲-𝔹 , ≲-𝔹 ⟩ = ∼-𝔹
  from ⟨ ≲-ℒ , ≲-ℒ ⟩ = ∼-ℒ
  from ⟨ ≲-Ref ℓ₁≾ℓ₂ ℓ₂≾ℓ₁ T₁≲T₂ T₂≲T₁ , ≲-Ref _ _ _ _ ⟩ =
    let ℓ₁~ℓ₂ = _⇔_.from (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ⟨ ℓ₁≾ℓ₂ , ℓ₂≾ℓ₁ ⟩ in
    let T₁∼T₂ = _⇔_.from (S∼T⇔S≲T×T≲S _ _) ⟨ T₁≲T₂ , T₂≲T₁ ⟩ in
      ∼-Ref ℓ₁~ℓ₂ T₁∼T₂
  from ⟨ ≲-Lab ℓ₁≾ℓ₂ T₁≲T₂ , ≲-Lab ℓ₂≾ℓ₁ T₂≲T₁ ⟩ =
    let ℓ₁~ℓ₂ = _⇔_.from (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ⟨ ℓ₁≾ℓ₂ , ℓ₂≾ℓ₁ ⟩ in
    let T₁∼T₂ = _⇔_.from (S∼T⇔S≲T×T≲S _ _) ⟨ T₁≲T₂ , T₂≲T₁ ⟩ in
      ∼-Lab ℓ₁~ℓ₂ T₁∼T₂
  from ⟨ ≲-⇒ ℓ₁′≾ℓ₁ ℓ₂≾ℓ₂′ T₁′≲T₁ T₂≲T₂′ , ≲-⇒ ℓ₁≾ℓ₁′ ℓ₂′≾ℓ₂ T₁≲T₁′ T₂′≲T₂ ⟩ =
    let ℓ₁~ℓ₁′ = _⇔_.from (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ⟨ ℓ₁≾ℓ₁′ , ℓ₁′≾ℓ₁ ⟩ in
    let ℓ₂~ℓ₂′ = _⇔_.from (ℓ~ℓ′⇔ℓ≾ℓ′×ℓ′≾ℓ _ _) ⟨ ℓ₂≾ℓ₂′ , ℓ₂′≾ℓ₂ ⟩ in
    let T₁∼T₁′ = _⇔_.from (S∼T⇔S≲T×T≲S _ _) ⟨ T₁≲T₁′ , T₁′≲T₁ ⟩ in
    let T₂∼T₂′ = _⇔_.from (S∼T⇔S≲T×T≲S _ _) ⟨ T₂≲T₂′ , T₂′≲T₂ ⟩ in
      ∼-⇒ ℓ₁~ℓ₁′ ℓ₂~ℓ₂′ T₁∼T₁′ T₂∼T₂′

-- Recall that label and type intersections are partial functions.
private
  ~→∏ : ∀ {ℓ̂₁ ℓ̂₂} → ℓ̂₁ ~ ℓ̂₂ → ∃[ ℓ̂ ] (ℓ̂₁ ∏ ℓ̂₂ ≡ just ℓ̂)
  ~→∏ {¿} ~-¿-r = ⟨ ¿ , refl ⟩
  ~→∏ {l̂ ℓ} ~-¿-r = ⟨ l̂ ℓ , refl ⟩
  ~→∏ {ℓ̂₂ = ¿} ~-¿-l = ⟨ ¿ , refl ⟩
  ~→∏ {ℓ̂₂ = l̂ ℓ} ~-¿-l = ⟨ l̂ ℓ , refl ⟩
  ~→∏ {l̂ ℓ} ~-l with ℓ ≟ ℓ
  ... | yes _ = ⟨ l̂ ℓ , refl ⟩
  ... | no ℓ≢ℓ = ⊥-elim (ℓ≢ℓ refl)

  ∼→∩ : ∀ {T₁ T₂} → T₁ ∼ T₂ → ∃[ S ] (T₁ ∩ T₂ ≡ just S)
  ∼→∩ ∼-⊤ = ⟨ `⊤ , refl ⟩
  ∼→∩ ∼-𝔹 = ⟨ `𝔹 , refl ⟩
  ∼→∩ ∼-ℒ = ⟨ `ℒ , refl ⟩
  ∼→∩ (∼-Ref ℓ₁~ℓ₂ T₁∼T₂) with ~→∏ ℓ₁~ℓ₂ | ∼→∩ T₁∼T₂
  ... | ⟨ ℓ̂ , eq₁ ⟩ | ⟨ T , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ Ref ℓ̂ T , refl ⟩
  ∼→∩ (∼-Lab ℓ₁~ℓ₂ T₁∼T₂) with ~→∏ ℓ₁~ℓ₂ | ∼→∩ T₁∼T₂
  ... | ⟨ ℓ̂ , eq₁ ⟩ | ⟨ T , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ Lab ℓ̂ T , refl ⟩
  ∼→∩ (∼-⇒ ℓ₁~ℓ₁′ ℓ₂~ℓ₂′ S₁∼T₁ S₂∼T₂) with ~→∏ ℓ₁~ℓ₁′ | ~→∏ ℓ₂~ℓ₂′ | ∼→∩ S₁∼T₁ | ∼→∩ S₂∼T₂
  ... | ⟨ ℓ̂₁″ , eq₁ ⟩ | ⟨ ℓ̂₂″ , eq₂ ⟩ | ⟨ T₁″ , eq₃ ⟩ | ⟨ T₂″ , eq₄ ⟩ rewrite eq₁ | eq₂ | eq₃ | eq₄ = ⟨ T₁″ [ ℓ̂₁″ ]⇒[ ℓ̂₂″ ] T₂″ , refl ⟩

  ∼→∨ : ∀ {T₁ T₂} → T₁ ∼ T₂ → ∃[ S ] (T₁ ∨ T₂ ≡ just S)
  ∼→∧ : ∀ {T₁ T₂} → T₁ ∼ T₂ → ∃[ S ] (T₁ ∧ T₂ ≡ just S)

  ∼→∨ ∼-⊤ = ⟨ `⊤ , refl ⟩
  ∼→∨ ∼-𝔹 = ⟨ `𝔹 , refl ⟩
  ∼→∨ ∼-ℒ = ⟨ `ℒ , refl ⟩
  ∼→∨ (∼-Ref ℓ₁~ℓ₂ T₁∼T₂) with ~→∏ ℓ₁~ℓ₂ | ∼→∩ T₁∼T₂
  ... | ⟨ ℓ̂ , eq₁ ⟩ | ⟨ T , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ Ref ℓ̂ T , refl ⟩
  ∼→∨ (∼-Lab ℓ₁~ℓ₂ T₁∼T₂) with ∼→∨ T₁∼T₂
  ... | ⟨ T , eq ⟩ rewrite eq = ⟨ Lab _ T , refl ⟩
  ∼→∨ (∼-⇒ ℓ₁~ℓ₁′ ℓ₂~ℓ₂′ S₁∼T₁ S₂∼T₂) with ∼→∧ S₁∼T₁ | ∼→∨ S₂∼T₂
  ... | ⟨ T₁″ , eq₁ ⟩ | ⟨ T₂″ , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ T₁″ [ _ ]⇒[ _ ] T₂″ , refl ⟩

  ∼→∧ ∼-⊤ = ⟨ `⊤ , refl ⟩
  ∼→∧ ∼-𝔹 = ⟨ `𝔹 , refl ⟩
  ∼→∧ ∼-ℒ = ⟨ `ℒ , refl ⟩
  ∼→∧ (∼-Ref ℓ₁~ℓ₂ T₁∼T₂) with ~→∏ ℓ₁~ℓ₂ | ∼→∩ T₁∼T₂
  ... | ⟨ ℓ̂ , eq₁ ⟩ | ⟨ T , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ Ref ℓ̂ T , refl ⟩
  ∼→∧ (∼-Lab ℓ₁~ℓ₂ T₁∼T₂) with ∼→∧ T₁∼T₂
  ... | ⟨ T , eq ⟩ rewrite eq = ⟨ Lab _ T , refl ⟩
  ∼→∧ (∼-⇒ ℓ₁~ℓ₁′ ℓ₂~ℓ₂′ S₁∼T₁ S₂∼T₂) with ∼→∨ S₁∼T₁ | ∼→∧ S₂∼T₂
  ... | ⟨ T₁″ , eq₁ ⟩ | ⟨ T₂″ , eq₂ ⟩ rewrite eq₁ | eq₂ = ⟨ T₁″ [ _ ]⇒[ _ ] T₂″ , refl ⟩

∏~ : ∀ {ℓ̂₁ ℓ̂₂} → ℓ̂₁ ~ ℓ̂₂ → ℒ̂
∏~ ℓ₁~ℓ₂ = proj₁ (~→∏ ℓ₁~ℓ₂)

∩∼ : ∀ {S T} → S ∼ T → 𝕋
∩∼ S∼T = proj₁ (∼→∩ S∼T)

∨∼ : ∀ {S T} → S ∼ T → 𝕋
∨∼ S∼T = proj₁ (∼→∨ S∼T)

∧∼ : ∀ {S T} → S ∼ T → 𝕋
∧∼ S∼T = proj₁ (∼→∧ S∼T)

private
  -- Tests:
  _ : ∃[ x ] (∏~ (~-l {l 42}) ≡ x)
  _ = ⟨ l̂ (l 42) , refl ⟩

  _ : ∃[ T ] (∩∼ (∼-Lab (~-¿-r {l̂ (l 42)}) ∼-⊤) ≡ T)
  _ = ⟨ Lab (l̂ (l 42)) `⊤ , refl ⟩
