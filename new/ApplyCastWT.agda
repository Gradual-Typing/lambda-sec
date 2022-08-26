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
    ----------------------------------
  → [] ; Σ ; gc ; pc ⊢ M ⦂ B
applycast-wt ⊢V v (A-base-id c) cast-base-id = ⊢value-pc ⊢V v
applycast-wt ⊢V v (A-base-proj _) (cast-base-proj ℓ₁≼ℓ₂) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (` ι of l ℓ₁) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
    W , refl , I-base-inj _ , ⊢W , <:-ty <:-⋆ <:-ι ⟩ →
      ⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ₁≼ℓ₂) <:-ι)
applycast-wt ⊢V v (A-base-proj _) (cast-base-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-fun (cast ([ _ ] C₁ ⇒ D₁ of ⋆) ([ _ ] C₂ ⇒ D₂ of ⋆) p _) A-id⋆) cast-fun-id⋆ =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ B<:C ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl B<:C))
applycast-wt ⊢V v (A-fun (cast ([ _ ] C₁ ⇒ D₁ of ⋆) ([ _ ] C₂ ⇒ D₂ of l _) p _) A-proj) (cast-fun-proj ℓ′≼ℓ) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ B<:C ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl B<:C))
applycast-wt ⊢V v a (cast-fun-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of l ℓ₁) ([ ⋆ ] D₁ ⇒ D₂ of g₂) p _) A-id⋆ I-label) cast-fun-pc-id⋆ =
  case ⟨ v , canonical-pc⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
applycast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of g₁) ([ l _ ] D₁ ⇒ D₂ of g₂) p _) A-proj I-label) (cast-fun-pc-proj pc≼pc′) =
  case ⟨ v , canonical-pc⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty <:ₗ-refl (<:-fun (<:-l pc≼pc′) <:-refl <:-refl))))
                  (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
applycast-wt ⊢V v a (cast-fun-pc-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-ref (cast (Ref C of ⋆) (Ref B of ⋆) p _) A-id⋆) cast-ref-id⋆ =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty <:-⋆ RefB<:RefC ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl RefB<:RefC))
applycast-wt ⊢V v (A-ref (cast (Ref C of ⋆) (Ref D of l _) p _) A-proj) (cast-ref-proj ℓ′≼ℓ) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty <:-⋆ RefB<:RefC ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl RefB<:RefC))
applycast-wt ⊢V v a (cast-ref-proj-blame _) = ⊢err
applycast-wt ⊢V v (A-ref-ref (cast (Ref (S of ⋆) of l _) (Ref (T of ⋆) of _) p _) A-id⋆ I-label) cast-ref-ref-id⋆ =
  case ⟨ v , canonical-ref⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty _ S′~T′))) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-ref (<:-ty <:-⋆ T′<:S) (<:-ty <:-⋆ S<:T′)) ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′))))
applycast-wt ⊢V v (A-ref-ref (cast (Ref (S of ⋆) of l _) (Ref (T of l _) of _) p _) A-proj I-label) (cast-ref-ref-proj refl) =
  case ⟨ v , canonical-ref⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty _ S′~T′))) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-ref (<:-ty <:-⋆ T′<:S) (<:-ty <:-⋆ S<:T′)) ⟩ →
      ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′))))
applycast-wt ⊢V v a (cast-ref-ref-proj-blame _) = ⊢err
