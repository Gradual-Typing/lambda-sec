module CC where

open import Data.Nat
open import Data.List
open import Data.Maybe
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

data Err : Term → Set where
  E-error : ∀ {e : Error} → Err (error e)

data Fun : Term → Set where
  Fun-ƛ : ∀ {gc A N ℓ} → Fun (ƛ[ gc ] A ˙ N of ℓ)
  Fun-proxy : ∀ {gc₁ gc₂ A B C D g₁ g₂ V}
                {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
    → Value V → Inert c
    → Fun (V ⟨ c ⟩)

data Refer : Term → Set where
  Ref-addr : ∀ {a ℓ} → Refer (addr a of ℓ)
  Ref-proxy : ∀ {A B g₁ g₂ V} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
    → Value V → Inert c
    → Refer (V ⟨ c ⟩)

canonical-fun : ∀ {Γ Σ gc gc′ A B g V}
  → Γ ; Σ ; gc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
  → Value V
  → Fun V
canonical-fun (⊢lam _) V-ƛ = Fun-ƛ
canonical-fun (⊢cast _) (V-cast v (I-fun c i)) = Fun-proxy v (I-fun c i)
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) v = canonical-fun ⊢V v

canonical-ref : ∀ {Γ Σ gc A g V}
  → Γ ; Σ ; gc ⊢ V ⦂ Ref A of g
  → Value V
  → Refer V
canonical-ref (⊢addr _) V-addr = Ref-addr
canonical-ref (⊢cast _) (V-cast v (I-ref c i)) = Ref-proxy v (I-ref c i)
canonical-ref (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) v = canonical-ref ⊢V v

canonical⋆ : ∀ {Γ Σ gc V T}
  → Γ ; Σ ; gc ⊢ V ⦂ T of ⋆
  → Value V
  → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ] (V ≡ W ⟨ c ⟩) × (Inert c) × (B <: T of ⋆)
canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = ⟨ _ , _ , ⟨ c , W , refl , i , <:-ty <:-⋆ <:ᵣ-refl ⟩ ⟩
canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , B , ⟨ c , W , refl , i , B<:T′⋆ ⟩ ⟩ →
      ⟨ A , B , ⟨ c , W , refl , i , <:-trans B<:T′⋆ (<:-ty <:-⋆ T′<:T) ⟩ ⟩

apply-cast : ∀ {Γ Σ gc A B} → (V : Term) → Γ ; Σ ; gc ⊢ V ⦂ A → Value V → (c : Cast A ⇒ B) → Active c → Term
-- V ⟨ ` ι of g ⇒ ` ι of g ⟩ —→ V
apply-cast V ⊢V v c (A-base-id .c) = V
apply-cast V ⊢V v c (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι))) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
                W , refl , I-base-inj _ , <:-ty <:-⋆ <:-ι ⟩ ⟩ →
      case ℓ′ ≼? ℓ of λ where
        (yes _) → V
        (no _) → error (blame p)
apply-cast V ⊢V v c (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ C~D)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
                W , refl , I-fun _ I-label , <:-ty <:-⋆ (<:-fun gc₁<:gc₂′ C₁<:B₁ B₂<:C₂) ⟩ ⟩ →
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
apply-cast V ⊢V v c (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , ⟨ cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
                W , refl , I-ref _ I-label , <:-ty <:-⋆ (<:-ref B<:C C<:B) ⟩ ⟩ →
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

-- A helper function to unwrap (inert) casts around a value
unwrap : ∀ V → Value V → Term
unwrap (V ⟨ c ⟩) (V-cast v i) = V
unwrap V _ = V

stamp-inert : ∀ {A B} → (c : Cast A ⇒ B) → Inert c → StaticLabel
                      → ∃[ C ] ∃[ D ] (Cast C ⇒ D)
stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι)) (I-base-inj _) ℓ =
  ⟨ _ , ⟨ _ , cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι) ⟩ ⟩
stamp-inert (cast ([ gc₁ ] A ⇒ B of g₁) ([ gc₂ ] C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
            (I-fun _ I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
    ⟨ _ , ⟨ _ , cast ([ gc₁ ] A ⇒ B of (g₁ ⋎̃ l ℓ)) ([ gc₂ ] C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~ ⟩ ⟩
stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB)) (I-ref _ I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
    ⟨ _ , ⟨ _ , cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~ ⟩ ⟩

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val (addr a of ℓ₁) V-addr ℓ = addr a of (ℓ₁ ⋎ ℓ)
stamp-val (ƛ[ pc ] A ˙ N of ℓ₁) V-ƛ ℓ = ƛ[ pc ] A ˙ N of (ℓ₁ ⋎ ℓ)
stamp-val ($ k of ℓ₁) V-const ℓ = $ k of (ℓ₁ ⋎ ℓ)
stamp-val (V ⟨ c ⟩) (V-cast v i) ℓ = let ⟨ C , D , c′ ⟩ = stamp-inert c i ℓ in V ⟨ c′ ⟩

-- Instantiation of gc to be low
⊢value-inst-gc : ∀ {Σ V A}
  → ∃[ gc ] [] ; Σ ; gc ⊢ V ⦂ A
  → Value V
  → [] ; Σ ; l low ⊢ V ⦂ A
⊢value-inst-gc ⟨ gc , ⊢addr eq ⟩ V-addr = ⊢addr eq
⊢value-inst-gc ⟨ gc , ⊢lam ⊢N ⟩ V-ƛ = ⊢lam ⊢N
⊢value-inst-gc ⟨ gc , ⊢const ⟩ V-const = ⊢const
⊢value-inst-gc ⟨ gc , ⊢cast ⊢V ⟩ (V-cast v i) = ⊢cast (⊢value-inst-gc ⟨ gc , ⊢V ⟩ v)
⊢value-inst-gc ⟨ gc , ⊢sub ⊢V A<:B ⟩ v = ⊢sub (⊢value-inst-gc ⟨ gc , ⊢V ⟩ v) A<:B

-- If an address is well-typed, the heap context lookup is successful.
⊢addr-lookup : ∀ {Γ Σ gc a ℓ A g}
  → Γ ; Σ ; gc ⊢ addr a of ℓ ⦂ Ref A of g
  → key _≟_ Σ a ≡ just A
⊢addr-lookup (⊢addr eq) = eq
⊢addr-lookup (⊢sub ⊢a (<:-ty _ (<:-ref A<:B B<:A)))
  rewrite <:-antisym A<:B B<:A = ⊢addr-lookup ⊢a
