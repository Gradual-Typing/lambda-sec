module WellTyped where

open import Data.Nat
open import Data.Unit using (⊤; tt)
open import Data.Bool using (true; false) renaming (Bool to 𝔹)
open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; subst; sym)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CC

{- TODO: move lemmas of well-typedness in CC to this module -}

apply-cast-wt : ∀ {Γ Σ gc pc A B V} {c : Cast A ⇒ B}
  → (⊢V : Γ ; Σ ; gc ; pc ⊢ V ⦂ A)
  → (v : Value V)
  → (a : Active c)
  → Γ ; Σ ; gc ; pc ⊢ apply-cast V ⊢V v c a ⦂ B
apply-cast-wt ⊢V v (A-base-id _) = ⊢V
apply-cast-wt ⊢V v (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι)))
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
        W , refl , I-base-inj _ , ⊢W , <:-ty <:-⋆ <:-ι ⟩
  with ℓ′ ≼? ℓ
...   | yes ℓ′≼ℓ = ⊢sub ⊢W (<:-ty (<:-l ℓ′≼ℓ) <:-ι)
...   | no  _ = ⊢err
apply-cast-wt ⊢V v (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ _)) a)
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
        W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ (<:-fun gc₁<:gc₂′ C₁<:B₁ B₂<:C₂) ⟩
  with a
...   | A-id⋆ = ⊢cast (⊢sub (⊢cast ⊢W) (<:-ty <:ₗ-refl (<:-fun gc₁<:gc₂′ C₁<:B₁ B₂<:C₂)))
...   | A-proj {ℓ} = {!!}
apply-cast-wt ⊢V v (A-fun-pc _ x x₁) = {!!}
apply-cast-wt ⊢V v (A-ref _ x) = {!!}
apply-cast-wt ⊢V v (A-ref-ref _ x x₁) = {!!}
