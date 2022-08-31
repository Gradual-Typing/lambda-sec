module ApplyCastWT where

open import Data.List hiding ([_])
open import Data.Product using (_×_; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CC
open import ApplyCastRelation

applycast-wt : ∀ {Σ gc pc A B V} {c : Cast A ⇒ B}
  → [] ; Σ ; l low ; low ⊢ V ⦂ A
  → Value V → Active c
    ----------------------------------
  → ∃[ M ] ApplyCast V , c ↝ M × [] ; Σ ; gc ; pc ⊢ M ⦂ B
applycast-wt ⊢V v (A-base-id c) = ⟨ _ , cast-base-id , ⊢value-pc ⊢V v ⟩
applycast-wt ⊢V v (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p _)) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
    W , refl , I-base-inj _ , ⊢W , <:-ty <:-⋆ <:-ι ⟩ →
      case ℓ′ ≼? ℓ of λ where
      (yes ℓ′≼ℓ) →
        ⟨ _ , cast-base-proj ℓ′≼ℓ , ⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:-ι) ⟩
      (no  ℓ′⋠ℓ) →
        ⟨ _ , cast-base-proj-blame ℓ′⋠ℓ , ⊢err ⟩
applycast-wt ⊢V v (A-fun (cast ([ _ ] C₁ ⇒ D₁ of ⋆) ([ _ ] C₂ ⇒ D₂ of g) p (~-ty _ d~)) a) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ B<:C ⟩ →
      case a of λ where
      A-id⋆ →
        let c~′ = ~-ty l~ A~B in
        let d~′ = ~-ty ~⋆ d~  in
        ⟨ _ , cast-fun-id⋆ {c~′ = c~′} {d~′} ,
          ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl B<:C)) ⟩
      (A-proj {ℓ}) →
        case ℓ′ ≼? ℓ of λ where
        (yes ℓ′≼ℓ) →
          let c~′ = ~-ty l~ A~B in
          let d~′ = ~-ty l~ d~  in
          ⟨ _ , cast-fun-proj {c~′ = c~′} {d~′} ℓ′≼ℓ ,
            ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl B<:C)) ⟩
        (no  ℓ′⋠ℓ) →
          ⟨ _ , cast-fun-proj-blame ℓ′⋠ℓ , ⊢err ⟩
applycast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of l ℓ₁) ([ gc ] D₁ ⇒ D₂ of g₂) p (~-ty ℓ₁~g₂ (~-fun _ C₁~C₂ D₁~D₂))) a I-label) =
  case ⟨ v , canonical-pc⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
    W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩ →
      case a of λ where
      A-id⋆ →
        let c~′ = ~-ty g₁′~g₂′ (~-fun l~ A₁~B₁ A₂~B₂) in
        let d~′ = ~-ty ℓ₁~g₂   (~-fun ~⋆ C₁~C₂ D₁~D₂) in
        ⟨ _ , cast-fun-pc-id⋆ {c~′ = c~′} {d~′} ,
          ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂))) ⟩
      (A-proj {pc}) →
        case pc ≼? pc′ of λ where
        (yes pc≼pc′) →
          let c~′ = ~-ty g₁′~g₂′ (~-fun l~ A₁~B₁ A₂~B₂) in
          let d~′ = ~-ty ℓ₁~g₂   (~-fun l~ C₁~C₂ D₁~D₂) in
          ⟨ _ , cast-fun-pc-proj {c~′ = c~′} {d~′} pc≼pc′ ,
            ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty <:ₗ-refl (<:-fun (<:-l pc≼pc′) <:-refl <:-refl))))
                  (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂))) ⟩
        (no  pc⋠pc′) → ⟨ _ , cast-fun-pc-proj-blame pc⋠pc′ , ⊢err ⟩
applycast-wt ⊢V v (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a) =
  case ⟨ v , canonical⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty <:-⋆ RefB<:RefC ⟩ →
      case a of λ where
      A-id⋆ →
        let c~′ = ~-ty l~ RefA~RefB in
        let d~′ = ~-ty ~⋆ RefC~RefD in
        ⟨ _ , cast-ref-id⋆ {c~′ = c~′} {d~′} ,
          ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl RefB<:RefC)) ⟩
      (A-proj {ℓ}) →
        case ℓ′ ≼? ℓ of λ where
        (yes ℓ′≼ℓ) →
          let c~′ = ~-ty l~ RefA~RefB in
          let d~′ = ~-ty l~ RefC~RefD in
          ⟨ _ , cast-ref-proj {c~′ = c~′} {d~′} ℓ′≼ℓ ,
            ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl RefB<:RefC)) ⟩
        (no  ℓ′⋠ℓ) → ⟨ _ , cast-ref-proj-blame ℓ′⋠ℓ , ⊢err ⟩
applycast-wt ⊢V v (A-ref-ref (cast (Ref (S of ⋆) of l ℓ₁) (Ref (T of g₂₁) of g₂) p (~-ty ℓ₁~g₂ (~-ref (~-ty _ S~T)))) a I-label) =
  case ⟨ v , canonical-ref⋆ ⊢V v ⟩ of λ where
  ⟨ V-cast w _ , _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty _ S′~T′))) ,
    W , refl , I-ref _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-ref (<:-ty <:-⋆ T′<:S) (<:-ty <:-⋆ S<:T′)) ⟩ →
      case a of λ where
      A-id⋆ →
        let c~′ = ~-ty g₁′~g₂′ (~-ref (~-ty l~ S′~T′)) in
        let d~′ = ~-ty ℓ₁~g₂   (~-ref (~-ty ~⋆ S~T)) in
        ⟨ _ , cast-ref-ref-id⋆ {c~′ = c~′} {d~′} ,
          ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′)))) ⟩
      (A-proj {ℓ₁}) →
        case ℓ₁′ =? ℓ₁ of λ where
        (yes refl) →
          let c~′ = ~-ty g₁′~g₂′ (~-ref (~-ty l~ S′~T′)) in
          let d~′ = ~-ty ℓ₁~g₂   (~-ref (~-ty l~ S~T)) in
          ⟨ _ , cast-ref-ref-proj {c~′ = c~′} {d~′} refl ,
            ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′)))) ⟩
        (no ℓ₁′≢ℓ₁) →
          ⟨ _ , cast-ref-ref-proj-blame ℓ₁′≢ℓ₁ , ⊢err ⟩
