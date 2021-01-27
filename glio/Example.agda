module Example where

open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import StaticsGLIO
open import Interp
open import Store
open import WellTypedness

Refl≼ : ∀ {𝓁} → 𝓁 ≼ 𝓁
Refl≼ {l x} = ≼-l ≤-refl

Refl≾ : ∀ {𝓁̂} → 𝓁̂ ≾ 𝓁̂
Refl≾ {¿} = ≾-¿-r
Refl≾ {l̂ _} = ≾-l Refl≼

{-
  A simple example:
    let _ = set x y in
      set z w
  where x, y, z, w are free vars (see Γ and γ).
-}
module SimpleExample where
  M : Term
  M = `let (set (` 0) (` 1)) (set (` 3) (` 4))

  Γ : Context
  Γ = Ref 𝐻̂ `⊤ ∷ `⊤ ∷ Ref 𝐿̂ `⊤ ∷ `⊤ ∷ []

  γ : Env
  γ = V-ref ⟨ 0 , 𝐿 , 𝐻 ⟩ ∷ V-tt ∷ V-ref ⟨ 1 , 𝐿 , 𝐿 ⟩ ∷ V-tt ∷ []

  μ : Store
  μ = ⟨ 0 , 𝐿 , 𝐻 ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷ ⟨ 1 , 𝐿 , 𝐿 ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷ []

  -- The env is well-typed under Γ, Σ.
  ⊢γ : Γ ∣ μ ⊢ₑ γ
  ⊢γ = ⊢ₑ∷ (⊢ᵥref refl) (⊢ₑ∷ ⊢ᵥtt (⊢ₑ∷ (⊢ᵥref refl) (⊢ₑ∷ ⊢ᵥtt ⊢ₑ∅)))

  -- The heap is well-typed under Σ.
  ⊢μ : μ ⊢ₛ μ
  ⊢μ = ⊢ₛ∷ ⊢ᵥtt (⊢ₛ∷ ⊢ᵥtt ⊢ₛ∅)

  -- The term with double heap assignments is well-typed under Γ.
  ⊢M : Γ [ 𝐿̂ , 𝐿̂ ]⊢ M ⦂ `⊤
  ⊢M = ⊢let (⊢set refl refl ≲-⊤ (≾-l (≼-l z≤n))) (⊢set refl refl ≲-⊤ (≾-l (≼-l z≤n))) ≲-⊤

  -- M runs okay.
  run : ∃[ conf ] (𝒱 γ M ⊢M μ 𝐿 10 ≡ result conf)
  run = ⟨ _ , refl ⟩

module LabExample where

  L : Term
  L = ƛ (` 0)

  ⊢L : ∀ {Γ} → Γ [ 𝐿̂ , 𝐿̂ ]⊢ L ⦂ (Lab 𝐿̂ `𝔹) [ 𝐿̂ ]⇒[ 𝐿̂ ] (Lab 𝐿̂ `𝔹)
  ⊢L = ⊢ƛ (⊢` refl)

  M : Term
  M = to-label 𝐻 `true

  ⊢M : ∀ {Γ} → Γ [ 𝐿̂ , 𝐿̂ ]⊢ M ⦂ Lab 𝐻̂ `𝔹
  ⊢M = ⊢to-label ⊢true (≾-l (≼-l z≤n))

  e : Term
  e = `let L (`let M (` 1 · ` 0))

  -- M̂ is labeled at runtime
  ê : Term
  ê = `let L (`let (to-label-dyn (` 1) `true) (` 1 · ` 0))

  ⊢ê : `ℒ ∷ [] [ 𝐿̂ , 𝐿̂ ]⊢ ê ⦂ Lab 𝐿̂ `𝔹
  ⊢ê = ⊢let ⊢L (⊢let (⊢to-label-dyn refl ⊢true) (⊢· refl refl (≲-Lab ≾-¿-r ≲-𝔹) Refl≾) (≲-Lab ≾-¿-r ≲-𝔹))
              (≲-⇒ Refl≾ Refl≾ (≲-Lab ≾-¿-l ≲-𝔹) (≲-Lab Refl≾ ≲-𝔹))

    -- This program is rejected statically because nothing inhabits 𝐻 ≼ 𝐿
  ⊢e : [] [ 𝐿̂ , 𝐿̂ ]⊢ e ⦂ Lab 𝐿̂ `𝔹
  ⊢e = ⊢let ⊢L (⊢let ⊢M (⊢· refl refl (≲-Lab Refl≾ ≲-𝔹) Refl≾) (≲-Lab Refl≾ ≲-𝔹))
             (≲-⇒ Refl≾ Refl≾ (≲-Lab (≾-l {!!}) ≲-𝔹) (≲-Lab Refl≾ ≲-𝔹))

  run : 𝒱 (V-label 𝐻 ∷ []) ê ⊢ê [] 𝐿 42 ≡ error castError
  run = refl

module RefExample where

  L : Term
  L = {!!}
