module ApplyCastWT where

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
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_
open import Values
open import ApplyCast



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
        W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ B<:C ⟩
  with a
...   | A-id⋆ = ⊢cast (⊢sub (⊢cast ⊢W) (<:-ty <:ₗ-refl B<:C))
...   | A-proj {ℓ}
  with ℓ′ ≼? ℓ
...     | yes ℓ′≼ℓ =
  ⊢cast (⊢sub (⊢cast (⊢sub ⊢W (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl B<:C))
...     | no  _    = ⊢err
apply-cast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of g₁) ([ gc ] D₁ ⇒ D₂ of g₂) p (~-ty g₁~g₂ (~-fun _ C₁~D₁ C₂~D₂))) a I-label)
  with canonical-pc⋆ ⊢V v
... | ⟨ _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
        W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩
  with a
...   | A-id⋆ = ⊢cast (⊢sub (⊢cast ⊢W) (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
...   | A-proj {pc}
  with pc ≼? pc′
...     | yes pc≼pc′ =
  ⊢cast (⊢sub (⊢cast (⊢sub ⊢W (<:-ty <:ₗ-refl (<:-fun (<:-l pc≼pc′) <:-refl <:-refl))))
              (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
...     | no  _      = ⊢err
apply-cast-wt ⊢V v (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a)
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
        W , refl , I-ref _ I-label I-label , ⊢W , <:-ty <:-⋆ RefB<:RefC ⟩
  with a
...   | A-id⋆ = ⊢cast (⊢sub (⊢cast ⊢W) (<:-ty <:ₗ-refl RefB<:RefC))
...   | A-proj {ℓ}
  with ℓ′ ≼? ℓ
...     | yes ℓ′≼ℓ =
  ⊢cast (⊢sub (⊢cast (⊢sub ⊢W (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl RefB<:RefC))
...     | no  _ = ⊢err
apply-cast-wt ⊢V v (A-ref-ref _ x x₁) = {!!}


