module Consistency where

open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)

open import StaticsGLIO
open import Lemmas using (≼-refl; ≼-antisym)
open import Iff using (_⇔_)



-- Consistency for labels
infixl 9 _~_

data _~_ : ℒ̂ → ℒ̂ → Set where

  ~-¿-r : ∀ {𝓁̂} → 𝓁̂ ~ ¿

  ~-¿-l : ∀ {𝓁̂} → ¿ ~ 𝓁̂

  ~-l : ∀ {𝓁} → (l̂ 𝓁) ~ (l̂ 𝓁)

-- Consistency for types
infixl 9 _∼_

data _∼_ : 𝕋 → 𝕋 → Set where

  ∼-⊤ : `⊤ ∼ `⊤

  ∼-𝔹 : `𝔹 ∼ `𝔹

  ∼-ℒ : `ℒ ∼ `ℒ

  ∼-Ref : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₂
    → T₁ ∼ T₂
      ----------------------
    → Ref 𝓁̂₁ T₁ ∼ Ref 𝓁̂₂ T₂

  ∼-Lab : ∀ {𝓁̂₁ 𝓁̂₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₂
    → T₁ ∼ T₂
      ----------------------
    → Lab 𝓁̂₁ T₁ ∼ Lab 𝓁̂₂ T₂

  ∼-⇒ : ∀ {𝓁̂₁ 𝓁̂₂ 𝓁̂₁′ 𝓁̂₂′ S₁ S₂ T₁ T₂}
    → 𝓁̂₁ ~ 𝓁̂₁′
    → 𝓁̂₂ ~ 𝓁̂₂′
    → S₁ ∼ T₁
    → S₂ ∼ T₂
      ---------------------------------------------------
    → (S₁ [ 𝓁̂₁ ]⇒[ 𝓁̂₂ ] S₂) ∼ (T₁ [ 𝓁̂₁′ ]⇒[ 𝓁̂₂′ ] T₂)

𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 : ∀ 𝓁̂ 𝓁̂′ → (𝓁̂ ~ 𝓁̂′) ⇔ (𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂)
𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 𝓁̂ 𝓁̂′ = record { to = to ; from = from }
  where
  to : 𝓁̂ ~ 𝓁̂′ → 𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂
  to ~-¿-r = ⟨ ≾-¿-r , ≾-¿-l ⟩
  to ~-¿-l = ⟨ ≾-¿-l , ≾-¿-r ⟩
  to ~-l = ⟨ ≾-l (≼-refl _) , ≾-l (≼-refl _) ⟩

  from : 𝓁̂ ≾ 𝓁̂′ × 𝓁̂′ ≾ 𝓁̂ → 𝓁̂ ~ 𝓁̂′
  from ⟨ ≾-¿-r , _ ⟩ = ~-¿-r
  from ⟨ ≾-¿-l , _ ⟩ = ~-¿-l
  from ⟨ ≾-l 𝓁≼𝓁′ , ≾-l 𝓁′≼𝓁 ⟩ rewrite ≼-antisym 𝓁≼𝓁′ 𝓁′≼𝓁 = ~-l

S∼T⇔S≾T×T≾S : ∀ S T → (S ∼ T) ⇔ (S ≲ T × T ≲ S)
S∼T⇔S≾T×T≾S S T = record { to = to ; from = from }
  where
  to : S ∼ T → S ≲ T × T ≲ S
  to ∼-⊤ = ⟨ ≲-⊤ , ≲-⊤ ⟩
  to ∼-𝔹 = ⟨ ≲-𝔹 , ≲-𝔹 ⟩
  to ∼-ℒ = ⟨ ≲-ℒ , ≲-ℒ ⟩
  to (∼-Ref 𝓁₁~𝓁₂ S∼T) =
    let ⟨ 𝓁₁≾𝓁₂ , 𝓁₂≾𝓁₁ ⟩ = _⇔_.to (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) 𝓁₁~𝓁₂ in
    let ⟨ T₁≲T₂ , T₂≲T₁ ⟩ = _⇔_.to (S∼T⇔S≾T×T≾S _ _) S∼T in
      ⟨ ≲-Ref 𝓁₁≾𝓁₂ 𝓁₂≾𝓁₁ T₁≲T₂ T₂≲T₁ , ≲-Ref 𝓁₂≾𝓁₁ 𝓁₁≾𝓁₂ T₂≲T₁ T₁≲T₂ ⟩
  to (∼-Lab 𝓁₁~𝓁₂ S∼T) =
    let ⟨ 𝓁₁≾𝓁₂ , 𝓁₂≾𝓁₁ ⟩ = _⇔_.to (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) 𝓁₁~𝓁₂ in
    let ⟨ T₁≲T₂ , T₂≲T₁ ⟩ = _⇔_.to (S∼T⇔S≾T×T≾S _ _) S∼T in
      ⟨ ≲-Lab 𝓁₁≾𝓁₂ T₁≲T₂ , ≲-Lab 𝓁₂≾𝓁₁ T₂≲T₁ ⟩
  to (∼-⇒ 𝓁₁~𝓁₁′ 𝓁₂~𝓁₂′ S₁∼T₁ S₂∼T₂) =
    let ⟨ 𝓁₁≾𝓁₁′ , 𝓁₁′≾𝓁₁ ⟩ = _⇔_.to (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) 𝓁₁~𝓁₁′ in
    let ⟨ 𝓁₂≾𝓁₂′ , 𝓁₂′≾𝓁₂ ⟩ = _⇔_.to (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) 𝓁₂~𝓁₂′ in
    let ⟨ S₁≲T₁ , T₁≲S₁ ⟩ = _⇔_.to (S∼T⇔S≾T×T≾S _ _) S₁∼T₁ in
    let ⟨ S₂≲T₂ , T₂≲S₂ ⟩ = _⇔_.to (S∼T⇔S≾T×T≾S _ _) S₂∼T₂ in
      ⟨ ≲-⇒ 𝓁₁′≾𝓁₁ 𝓁₂≾𝓁₂′ T₁≲S₁ S₂≲T₂ , ≲-⇒ 𝓁₁≾𝓁₁′ 𝓁₂′≾𝓁₂ S₁≲T₁ T₂≲S₂ ⟩

  from : S ≲ T × T ≲ S → S ∼ T
  from ⟨ ≲-⊤ , ≲-⊤ ⟩ = ∼-⊤
  from ⟨ ≲-𝔹 , ≲-𝔹 ⟩ = ∼-𝔹
  from ⟨ ≲-ℒ , ≲-ℒ ⟩ = ∼-ℒ
  from ⟨ ≲-Ref 𝓁₁≾𝓁₂ 𝓁₂≾𝓁₁ T₁≲T₂ T₂≲T₁ , ≲-Ref _ _ _ _ ⟩ =
    let 𝓁₁~𝓁₂ = _⇔_.from (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) ⟨ 𝓁₁≾𝓁₂ , 𝓁₂≾𝓁₁ ⟩ in
    let T₁∼T₂ = _⇔_.from (S∼T⇔S≾T×T≾S _ _) ⟨ T₁≲T₂ , T₂≲T₁ ⟩ in
      ∼-Ref 𝓁₁~𝓁₂ T₁∼T₂
  from ⟨ ≲-Lab 𝓁₁≾𝓁₂ T₁≲T₂ , ≲-Lab 𝓁₂≾𝓁₁ T₂≲T₁ ⟩ =
    let 𝓁₁~𝓁₂ = _⇔_.from (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) ⟨ 𝓁₁≾𝓁₂ , 𝓁₂≾𝓁₁ ⟩ in
    let T₁∼T₂ = _⇔_.from (S∼T⇔S≾T×T≾S _ _) ⟨ T₁≲T₂ , T₂≲T₁ ⟩ in
      ∼-Lab 𝓁₁~𝓁₂ T₁∼T₂
  from ⟨ ≲-⇒ 𝓁₁′≾𝓁₁ 𝓁₂≾𝓁₂′ T₁′≲T₁ T₂≲T₂′ , ≲-⇒ 𝓁₁≾𝓁₁′ 𝓁₂′≾𝓁₂ T₁≲T₁′ T₂′≲T₂ ⟩ =
    let 𝓁₁~𝓁₁′ = _⇔_.from (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) ⟨ 𝓁₁≾𝓁₁′ , 𝓁₁′≾𝓁₁ ⟩ in
    let 𝓁₂~𝓁₂′ = _⇔_.from (𝓁~𝓁′⇔𝓁≾𝓁′×𝓁′≾𝓁 _ _) ⟨ 𝓁₂≾𝓁₂′ , 𝓁₂′≾𝓁₂ ⟩ in
    let T₁∼T₁′ = _⇔_.from (S∼T⇔S≾T×T≾S _ _) ⟨ T₁≲T₁′ , T₁′≲T₁ ⟩ in
    let T₂∼T₂′ = _⇔_.from (S∼T⇔S≾T×T≾S _ _) ⟨ T₂≲T₂′ , T₂′≲T₂ ⟩ in
      ∼-⇒ 𝓁₁~𝓁₁′ 𝓁₂~𝓁₂′ T₁∼T₁′ T₂∼T₂′
