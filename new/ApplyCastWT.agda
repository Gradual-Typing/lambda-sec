module ApplyCastWT where

open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CC
open import ApplyCastRelation

applycast-wt : ∀ {Σ gc pc A B V M} {c : Cast A ⇒ B}
  → [] ; Σ ; l low ; low ⊢ V ⦂ A
  → Value V → Active c
  → ApplyCast V , c ↝ M
    -----------------------------
  → [] ; Σ ; gc ; pc ⊢ M ⦂ B
applycast-wt ⊢V v (A-base-id c) cast-base-id = ⊢value-pc ⊢V v
applycast-wt ⊢V v (A-base-proj _) (cast-base-proj ℓ₁≼ℓ₂) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (` ι of l ℓ₁) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
    W , refl , I-base-inj _ , ⊢W , <:-ty <:-⋆ <:-ι ⟩ →
    ⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)
applycast-wt ⊢V v (A-base-proj _) (cast-base-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-fun .(cast ([ _ ] _ ⇒ _ of ⋆) ([ _ ] _ ⇒ _ of ⋆) _ _) A-id⋆) cast-fun-id⋆ = {!!}
applycast-wt ⊢V v (A-fun .(cast ([ _ ] _ ⇒ _ of ⋆) ([ _ ] _ ⇒ _ of l _) _ _) A-proj) (cast-fun-proj ℓ₁≼ℓ₄) = {!!}
applycast-wt ⊢V v a (cast-fun-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of l ℓ₁) ([ ⋆ ] D₁ ⇒ D₂ of g₂) p _) A-id⋆ I-label) cast-fun-pc-id⋆ =
  case ⟨ v , canonical-pc⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
applycast-wt ⊢V v a (cast-fun-pc-proj x) = {!!}
applycast-wt ⊢V v a (cast-fun-pc-proj-blame _) = ⊢err
applycast-wt ⊢V v a cast-ref-id⋆ = {!!}
applycast-wt ⊢V v a (cast-ref-proj x) = {!!}
applycast-wt ⊢V v a (cast-ref-proj-blame _) = ⊢err
applycast-wt ⊢V v a cast-ref-ref-id⋆ = {!!}
applycast-wt ⊢V v a (cast-ref-ref-proj x) = {!!}
applycast-wt ⊢V v a (cast-ref-ref-proj-blame _) = ⊢err
