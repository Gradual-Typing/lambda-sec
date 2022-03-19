module CC where

open import Data.List
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax) renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_ public
open import CCTyping Cast_⇒_ public
open import Utils


data Value : Term → Set where
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {pc A N ℓ} → Value (ƛ[ pc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)

-- TODO: change the signature to be more like pc⋆
canonical⋆ : ∀ {Γ Σ gc V T}
  → Γ ; Σ ; gc ⊢ V ⦂ T of ⋆
  → Value V
  → ∃[ A ] ∃[ T′ ] Σ[ c ∈ Cast A ⇒ (T′ of ⋆) ] ∃[ W ] (V ≡ W ⟨ c ⟩) × (Inert c) × (T′ <:ᵣ T)
canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = ⟨ _ , _ , ⟨ c , W , refl , i , <:ᵣ-refl ⟩ ⟩
canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , T″ , ⟨ c , W , refl , i , T″<:T′ ⟩ ⟩ →
      ⟨ A , T″ , ⟨ c , W , refl , i , <:ᵣ-trans T″<:T′ T′<:T ⟩ ⟩

canonical-pc⋆ : ∀ {Γ Σ gc V A B g}
  → Γ ; Σ ; gc ⊢ V ⦂ [ ⋆ ] A ⇒ B of g
  → Value V
  → ∃[ C ] ∃[ D ] Σ[ c ∈ Cast C ⇒ D ] ∃[ W ] (V ≡ W ⟨ c ⟩) × (Inert c) × (D <: [ ⋆ ] A ⇒ B of g)
canonical-pc⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = ⟨ _ , _ , ⟨ c , W , refl , i , <:-refl ⟩ ⟩
canonical-pc⋆ (⊢sub {A = [ ⋆ ] A′ ⇒ B′ of g′} ⊢V (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B))) v =
  case canonical-pc⋆ ⊢V v of λ where
    ⟨ C , D , ⟨ c , W , refl , i , D<:A′→B′ ⟩ ⟩ →
      let D<:A→B = <:-trans D<:A′→B′ (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B)) in
        ⟨ C , D , ⟨ c , W , refl , i , D<:A→B ⟩ ⟩

apply-cast : ∀ {Γ Σ gc A B} → (V : Term) → Γ ; Σ ; gc ⊢ V ⦂ A → Value V → (c : Cast A ⇒ B) → Active c → Term
-- V ⟨ ` ι of g ⇒ ` ι of g ⟩ —→ V
apply-cast V ⊢V v c (A-base-id .c) = V
apply-cast V ⊢V v c (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι))) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
                W , refl , I-base-inj _ , <:-ι ⟩ ⟩ →
      case ℓ′ ≼? ℓ of λ where
        (yes _) → V
        (no _) → error (blame p)
{- Order of reduction:
        V ⟨ [ pc′ ] A₁ → A₂ of ℓ′ ⇒ [ ⋆ ] B₁ → B₂ of ⋆ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ⋆ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩
   —→ V ⟨ [ pc′ ] A₁ → A₂ of ℓ  ⇒ [ ⋆ ] B₁ → B₂ of ℓ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩  , if ℓ′ ≼ ℓ
   —→ V ⟨ [ pc  ] A₁ → A₂ of ℓ  ⇒ [ pc ] B₁ → B₂ of ℓ ⟩ ⟨ [ pc ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩ , if pc ≼ pc′
   -}
apply-cast V ⊢V v c (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ C~D)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
                W , refl , I-fun _ I-label I-label , <:-fun gc₁<:gc₂′ C₁<:B₁ B₂<:C₂ ⟩ ⟩ →
      case a of λ where
        -- We don't touch the security effects in this case, only propagate the labels on types
        --      W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ⋆  ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ⋆  ⇒ [ gc₂ ] D₁ → D₂ of ⋆ ⟩
        -- —→ W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ℓ′ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ℓ′ ⇒ [ gc₂ ] D₁ → D₂ of ⋆ ⟩
        A-id⋆ →
          let c~₁ = ~-ty ~ₗ-refl A~B
              c~₂ = ~-ty ~⋆      C~D in
            W ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of l ℓ′) q c~₁ ⟩
              ⟨ cast ([ gc₁  ] C₁ ⇒ C₂ of l ℓ′) ([ gc₂  ] D₁ ⇒ D₂ of ⋆   ) p c~₂ ⟩
        --      W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ′ ⇒ [ gc₂′ ] B₁ → B₂ of ⋆ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ⋆ ⇒ [ gc₂ ] D₁ → D₂ of ℓ ⟩
        -- —→ W ⟨ [ gc₁′ ] A₁ → A₂ of ℓ  ⇒ [ gc₂′ ] B₁ → B₂ of ℓ ⟩ ⟨ [ gc₁ ] C₁ → C₂ of ℓ ⇒ [ gc₂ ] D₁ → D₂ of ℓ ⟩  , if ℓ′ ≼ ℓ
        --      blame p  , otherwise
        (A-proj {ℓ}) →
          case ℓ′ ≼? ℓ of λ where
            (yes _) →
              let c~₁ = ~-ty ~ₗ-refl A~B
                  c~₂ = ~-ty ~ₗ-refl C~D in
                W ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ) ([ gc₂′ ] B₁ ⇒ B₂ of l ℓ) q c~₁ ⟩
                  ⟨ cast ([ gc₁  ] C₁ ⇒ C₂ of l ℓ) ([ gc₂  ] D₁ ⇒ D₂ of l ℓ) p c~₂ ⟩
            (no _) → error (blame p)
apply-cast V ⊢V v c (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of g₁) ([ gc ] D₁ ⇒ D₂ of g₂) p (~-ty g₁~g₂ (~-fun _ C₁~D₁ C₂~D₂))) a I-label) =
  case canonical-pc⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun ~⋆ A₁~B₁ A₂~B₂)) ,
                W , refl , I-fun _ I-label I-label , <:-ty _ (<:-fun <:-⋆ _ _) ⟩ ⟩ →
      case a of λ where
        -- We don't touch the labels on types, only propagate the security effects
        --      W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ ⋆   ] B₁ → B₂ of g₂′ ⟩ ⟨ [ ⋆   ] C₁ → C₂ of g₁ ⇒ [ ⋆ ] D₁ → D₂ of g₂ ⟩
        -- —→ W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ pc′ ] B₁ → B₂ of g₂′ ⟩ ⟨ [ pc′ ] C₁ → C₂ of g₁ ⇒ [ ⋆ ] D₁ → D₂ of g₂ ⟩
        A-id⋆ →
          let c~₁ = ~-ty g₁′~g₂′ (~-fun ~ₗ-refl A₁~B₁ A₂~B₂)
              c~₂ = ~-ty g₁~g₂ (~-fun ~⋆ C₁~D₁ C₂~D₂) in
            W ⟨ cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ l pc′ ] B₁ ⇒ B₂ of g₂′) q c~₁ ⟩
              ⟨ cast ([ l pc′ ] C₁ ⇒ C₂ of g₁) ([ ⋆ ] D₁ ⇒ D₂ of g₂) p c~₂ ⟩
        --      W ⟨ [ pc′ ] A₁ → A₂ of g₁′ ⇒ [ ⋆  ] B₁ → B₂ of g₂′ ⟩ ⟨ [ ⋆  ] C₁ → C₂ of g₁ ⇒ [ pc ] D₁ → D₂ of g₂ ⟩
        -- —→ W ⟨ [ pc  ] A₁ → A₂ of g₁′ ⇒ [ pc ] B₁ → B₂ of g₂′ ⟩ ⟨ [ pc ] C₁ → C₂ of g₁ ⇒ [ pc ] D₁ → D₂ of g₂ ⟩  , if pc ≼ pc′
        --      blame p  , otherwise
        (A-proj {pc}) →
          case pc ≼? pc′ of λ where
            (yes _) →
              let c~₁ = ~-ty g₁′~g₂′ (~-fun ~ₗ-refl A₁~B₁ A₂~B₂)
                  c~₂ = ~-ty g₁~g₂ (~-fun ~ₗ-refl C₁~D₁ C₂~D₂) in
              W ⟨ cast ([ l pc ] A₁ ⇒ A₂ of g₁′) ([ l pc ] B₁ ⇒ B₂ of g₂′) q c~₁ ⟩
                ⟨ cast ([ l pc ] C₁ ⇒ C₂ of g₁ ) ([ l pc ] D₁ ⇒ D₂ of g₂ ) p c~₂ ⟩
            (no _) → error (blame p)
apply-cast V ⊢V v c (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
                W , refl , I-ref _ I-label , <:-ref B<:C C<:B ⟩ ⟩ →
      case a of λ where
        --      W ⟨ Ref A of ℓ′ ⇒ Ref B of ⋆  ⟩ ⟨ Ref C of ⋆  ⇒ Ref D of ⋆ ⟩
        -- —→ W ⟨ Ref A of ℓ′ ⇒ Ref B of ℓ′ ⟩ ⟨ Ref C of ℓ′ ⇒ Ref D of ⋆ ⟩
        A-id⋆ →
          let c~₁ = ~-ty ~ₗ-refl RefA~RefB
              c~₂ = ~-ty ~⋆      RefC~RefD in
            W ⟨ cast (Ref A of l ℓ′) (Ref B of l ℓ′) q c~₁ ⟩ ⟨ cast (Ref C of l ℓ′) (Ref D of ⋆) p c~₂ ⟩
        --      W ⟨ Ref A of ℓ′ ⇒ Ref B of ⋆ ⟩ ⟨ Ref C of ⋆ ⇒ Ref D of ℓ ⟩
        -- —→ W ⟨ Ref A of ℓ  ⇒ Ref B of ℓ ⟩ ⟨ Ref C of ℓ ⇒ Ref D of ℓ ⟩  , if ℓ′ ≼ ℓ
        --      blame p                                                       , otherwise
        (A-proj {ℓ}) →
          case ℓ′ ≼? ℓ of λ where
            (yes _) →
              let c~₁ = ~-ty ~ₗ-refl RefA~RefB
                  c~₂ = ~-ty ~ₗ-refl RefC~RefD in
                W ⟨ cast (Ref A of l ℓ) (Ref B of l ℓ) q c~₁ ⟩ ⟨ cast (Ref C of l ℓ) (Ref D of l ℓ) p c~₂ ⟩
            (no _) → error (blame p)
