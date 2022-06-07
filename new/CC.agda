module CC where

open import Data.Nat
open import Data.Bool renaming (Bool to 𝔹; _≟_ to _≟ᵇ_)
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
  V-ƛ : ∀ {gc A N ℓ} → Value (ƛ[ gc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)

data Err : Term → Set where
  E-error : ∀ {e : Error} → Err (error e)

data Fun : Term → HeapContext → Type → Set where
  Fun-ƛ : ∀ {Σ gc pc′ A A′ B B′ g N ℓ}
    → (∀ {pc} → A′ ∷ [] ; Σ ; l pc′ ; pc ⊢ N ⦂ B′)
    → [ l pc′ ] A′ ⇒ B′ of l ℓ <: [ gc ] A ⇒ B of g
      ----------------------------------------------------- Lambda
    → Fun (ƛ[ pc′ ] A′ ˙ N of ℓ) Σ ([ gc ] A ⇒ B of g)

  Fun-proxy : ∀ {Σ gc gc₁ gc₂ A A₁ A₂ B B₁ B₂ g g₁ g₂ V}
                {c : Cast ([ gc₁ ] A₁ ⇒ B₁ of g₁) ⇒ ([ gc₂ ] A₂ ⇒ B₂ of g₂)}
    → Fun V Σ ([ gc₁ ] A₁ ⇒ B₁ of g₁)
    → Inert c
    → [ gc₂ ] A₂ ⇒ B₂ of g₂ <: [ gc ] A ⇒ B of g
      ----------------------------------------------------- Function Proxy
    → Fun (V ⟨ c ⟩) Σ ([ gc ] A ⇒ B of g)

-- Sanity checks
fun-is-value : ∀ {Σ V gc A B g}
  → Fun V Σ ([ gc ] A ⇒ B of g)
  → Value V
fun-is-value (Fun-ƛ _ sub) = V-ƛ
fun-is-value (Fun-proxy fun i _) = V-cast (fun-is-value fun) i

fun-wt : ∀ {Σ V gc gc′ pc A B g}
  → Fun V Σ ([ gc′ ] A ⇒ B of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
fun-wt (Fun-ƛ {Σ} ⊢N sub) = ⊢sub (⊢lam ⊢N) sub
fun-wt (Fun-proxy fun i sub) = ⊢sub (⊢cast (fun-wt fun)) sub

-- Canonical form of value of function type
canonical-fun : ∀ {Σ gc gc′ pc A B g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
  → Value V
  → Fun V Σ ([ gc′ ] A ⇒ B of g)
canonical-fun (⊢lam ⊢N) V-ƛ = Fun-ƛ ⊢N <:-refl
canonical-fun (⊢cast ⊢V) (V-cast v (I-fun c i₁ i₂)) =
  Fun-proxy (canonical-fun ⊢V v) (I-fun c i₁ i₂) <:-refl
canonical-fun (⊢sub ⊢V sub) v =
  case sub of λ where
    (<:-ty _ (<:-fun _ _ _)) →
      case canonical-fun ⊢V v of λ where
        (Fun-ƛ ⊢N sub₁)        → Fun-ƛ ⊢N (<:-trans sub₁ sub)
        (Fun-proxy fun i sub₁) → Fun-proxy fun i (<:-trans sub₁ sub)
canonical-fun (⊢sub-pc ⊢V gc<:gc′) v = canonical-fun ⊢V v

data Reference : Term → HeapContext → Type → Set where
  Ref-addr : ∀ {Σ A a T g ℓ ℓ₁}
    → key _≟_ Σ a ≡ just ⟨ T , ℓ₁ ⟩
    → Ref (T of l ℓ₁) of l ℓ <: Ref A of g
      ---------------------------------------- Reference
    → Reference (addr a of ℓ) Σ (Ref A of g)

  Ref-proxy : ∀ {Σ A A₁ A₂ g g₁ g₂ V} {c : Cast (Ref A₁ of g₁) ⇒ (Ref A₂ of g₂)}
    → Reference V Σ (Ref A₁ of g₁)
    → Inert c
    → Ref A₂ of g₂ <: Ref A of g
      ---------------------------------------- Reference proxy
    → Reference (V ⟨ c ⟩) Σ (Ref A of g)

ref-is-value : ∀ {Σ V A g}
  → Reference V Σ (Ref A of g)
  → Value V
ref-is-value (Ref-addr _ _) = V-addr
ref-is-value (Ref-proxy ref i _) = V-cast (ref-is-value ref) i

ref-wt : ∀ {Σ V gc pc A g}
  → Reference V Σ (Ref A of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
ref-wt (Ref-addr eq sub) = ⊢sub (⊢addr eq) sub
ref-wt (Ref-proxy ref i sub) = ⊢sub (⊢cast (ref-wt ref)) sub

canonical-ref : ∀ {Σ gc pc A g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
  → Value V
  → Reference V Σ (Ref A of g)
canonical-ref (⊢addr eq) V-addr = Ref-addr eq <:-refl
canonical-ref (⊢cast ⊢V) (V-cast v (I-ref c i₁ i₂)) =
  Ref-proxy (canonical-ref ⊢V v) (I-ref c i₁ i₂) <:-refl
canonical-ref (⊢sub ⊢V sub) v =
  case sub of λ where
    (<:-ty _ (<:-ref _ _)) →
      case canonical-ref ⊢V v of λ where
        (Ref-addr eq sub₁) → Ref-addr eq (<:-trans sub₁ sub)
        (Ref-proxy ref i sub₁) → Ref-proxy ref i (<:-trans sub₁ sub)
canonical-ref (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref ⊢V v

data Constant : Term → Type → Set where
  Const-base : ∀ {ι} {k : rep ι} {ℓ ℓ′}
    → ℓ ≼ ℓ′
      ------------------------------- Constant
    → Constant ($ k of ℓ) (` ι of l ℓ′)

  Const-inj : ∀ {ι} {k : rep ι} {ℓ ℓ′} {c : Cast (` ι of l ℓ′) ⇒ (` ι of ⋆)}
    → ℓ ≼ ℓ′
      ------------------------------- Injected constant
    → Constant ($ k of ℓ ⟨ c ⟩) (` ι of ⋆)

-- The labels on a constant and its type are related by subtyping.
const-label-≼ : ∀ {Γ Σ gc pc ι} {k : rep ι} {ℓ g}
  → Γ ; Σ ; gc ; pc ⊢ $ k of ℓ ⦂ ` ι of g
  → ∃[ ℓ′ ] (g ≡ l ℓ′) × (ℓ ≼ ℓ′)
const-label-≼ {ℓ = ℓ} ⊢const = ⟨ ℓ , refl , ≼-refl ⟩
const-label-≼ (⊢sub ⊢M (<:-ty ℓ′<:g <:-ι)) =
  case ⟨ const-label-≼ ⊢M , ℓ′<:g ⟩ of λ where
    ⟨ ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ , <:-l ℓ′≼ℓ″ ⟩ →
      ⟨ _ , refl , ≼-trans ℓ≼ℓ′ ℓ′≼ℓ″ ⟩
const-label-≼ (⊢sub-pc ⊢M gc<:gc′) = const-label-≼ ⊢M

canonical-const : ∀ {Σ gc pc ι g V}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ ` ι of g
  → Value V
  → Constant V (` ι of g)
canonical-const ⊢const V-const = (Const-base ≼-refl)
canonical-const (⊢cast ⊢V) (V-cast v (I-base-inj c)) =
  case canonical-const ⊢V v of λ where
    (Const-base _) →
      case const-label-≼ ⊢V of λ where
        ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ → Const-inj ℓ≼ℓ′
canonical-const (⊢sub ⊢V (<:-ty ℓ′<:g <:-ι)) v =
  case ⟨ canonical-const ⊢V v , ℓ′<:g ⟩ of λ where
    ⟨ Const-base ℓ≼ℓ′ , <:-l ℓ′≼ℓ″ ⟩ → Const-base (≼-trans ℓ≼ℓ′ ℓ′≼ℓ″)
    ⟨ Const-inj  ℓ≼ℓ′ , <:-⋆ ⟩ → Const-inj ℓ≼ℓ′
canonical-const (⊢sub-pc ⊢V _) v = canonical-const ⊢V v

canonical⋆ : ∀ {Γ Σ gc pc V T}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ T of ⋆
  → Value V
  → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Inert c) × (B <: T of ⋆)
canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , <:-ty <:-⋆ <:ᵣ-refl ⟩
canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , B , c , W , refl , i , B<:T′⋆ ⟩ →
      ⟨ A , B , c , W , refl , i , <:-trans B<:T′⋆ (<:-ty <:-⋆ T′<:T) ⟩
canonical⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical⋆ ⊢V v

canonical-pc⋆ : ∀ {Γ Σ gc pc V A B g}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ [ ⋆ ] A ⇒ B of g
  → Value V
  → ∃[ C ] ∃[ D ] Σ[ c ∈ Cast C ⇒ D ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Inert c) × (D <: [ ⋆ ] A ⇒ B of g)
canonical-pc⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , <:-refl ⟩
canonical-pc⋆ (⊢sub ⊢V (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B))) v =
  case canonical-pc⋆ ⊢V v of λ where
    ⟨ C , D , c , W , refl , i , D<:A′→B′ ⟩ →
      let D<:A→B = <:-trans D<:A′→B′ (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B)) in
        ⟨ C , D , c , W , refl , i , D<:A→B ⟩
canonical-pc⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical-pc⋆ ⊢V v

canonical-ref⋆ : ∀ {Γ Σ gc pc V T g}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ Ref (T of ⋆) of g
  → Value V
  → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Inert c) × (B <: Ref (T of ⋆) of g)
canonical-ref⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , <:-refl ⟩
canonical-ref⋆ (⊢sub ⊢V sub) v =
  case sub of λ where
    (<:-ty _ (<:-ref (<:-ty <:-⋆ S<:T) (<:-ty <:-⋆ T<:S))) →
      case canonical-ref⋆ ⊢V v of λ where
        ⟨ A , B , c , W , refl , i , B<:RefS ⟩ →
          ⟨ A , B , c , W , refl , i , <:-trans B<:RefS sub ⟩
canonical-ref⋆ (⊢sub-pc ⊢V gc<:gc′) v = canonical-ref⋆ ⊢V v

apply-cast : ∀ {Γ Σ gc pc A B}
  → (V : Term) → Γ ; Σ ; gc ; pc ⊢ V ⦂ A → Value V
  → (c : Cast A ⇒ B) → Active c → Term
-- V ⟨ ` ι of g ⇒ ` ι of g ⟩ —→ V
apply-cast V ⊢V v c (A-base-id .c) = V
apply-cast V ⊢V v c (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι))) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
      W , refl , I-base-inj _ , <:-ty <:-⋆ <:-ι ⟩ →
      case ℓ′ ≼? ℓ of λ where
        (yes _) → V
        (no _) → error (blame p)
{- Order of reduction: propagate label first and then the security effect
        V ⟨ [ pc′ ] A₁ → A₂ of ℓ′ ⇒ [ ⋆ ] B₁ → B₂ of ⋆ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ⋆ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩
   —→ V ⟨ [ pc′ ] A₁ → A₂ of ℓ  ⇒ [ ⋆ ] B₁ → B₂ of ℓ ⟩ ⟨ [ ⋆ ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩   , if ℓ′ ≼ ℓ
   —→ V ⟨ [ pc  ] A₁ → A₂ of ℓ  ⇒ [ pc ] B₁ → B₂ of ℓ ⟩ ⟨ [ pc ] C₁ → C₂ of ℓ ⇒ [ pc ] D₁ → D₂ of ℓ ⟩ , if pc ≼ pc′
   -}
apply-cast V ⊢V v c (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ C~D)) a) =
  case canonical⋆ ⊢V v of λ where
    ⟨ _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
      W , refl , I-fun _ I-label I-label , <:-ty <:-⋆ (<:-fun gc₁<:gc₂′ C₁<:B₁ B₂<:C₂) ⟩ →
      case a of λ where
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
    ⟨ _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun ~⋆ A₁~B₁ A₂~B₂)) ,
      W , refl , I-fun _ I-label I-label , <:-ty _ (<:-fun <:-⋆ _ _) ⟩ →
      case a of λ where
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
    ⟨ _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
      W , refl , I-ref _ I-label I-label , <:-ty <:-⋆ (<:-ref B<:C C<:B) ⟩ →
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
apply-cast V ⊢V v c (A-ref-ref (cast (Ref (S of ⋆) of g₁) (Ref (T of g₂₁) of g₂) p (~-ty g₁~g₂ (~-ref (~-ty _ S~T)))) a I-label) =
  case canonical-ref⋆ ⊢V v of λ where
    ⟨ _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty ~⋆ S′~T′))) ,
      W , refl , I-ref _ I-label I-label , <:-ty _ (<:-ref (<:-ty <:-⋆ _) (<:-ty <:-⋆ _)) ⟩ →
      case a of λ where
        --      W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of  ⋆ ) of g₂′ ⟩ ⟨ Ref (S of  ⋆ ) of g₁ ⇒ Ref (T of ⋆) of g₂ ⟩
        -- —→ W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of ℓ₁′) of g₂′ ⟩ ⟨ Ref (S of ℓ₁′) of g₁ ⇒ Ref (T of ⋆) of g₂ ⟩
        A-id⋆ →
          let c~₁ = ~-ty g₁′~g₂′ (~-ref (~-ty ~ₗ-refl S′~T′))
              c~₂ = ~-ty g₁~g₂ (~-ref (~-ty ~⋆ S~T)) in
          W ⟨ cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of l ℓ₁′) of g₂′) q c~₁ ⟩
            ⟨ cast (Ref (S of l ℓ₁′) of g₁) (Ref (T of ⋆) of g₂) p c~₂ ⟩
        --      W ⟨ Ref (S′ of ℓ₁′) of g₁′ ⇒ Ref (T′ of  ⋆ ) of g₂′ ⟩ ⟨ Ref (S of  ⋆ ) of g₁ ⇒ Ref (T of ℓ₁) of g₂ ⟩
        -- —→ W ⟨ Ref (S′ of ℓ₁ ) of g₁′ ⇒ Ref (T′ of  ℓ₁) of g₂′ ⟩ ⟨ Ref (S of  ℓ₁) of g₁ ⇒ Ref (T of ℓ₁) of g₂ ⟩ , if ℓ₁′ = ℓ₁
        --      blame p  , otherwise
        (A-proj {ℓ₁}) →
          case ℓ₁′ =? ℓ₁ of λ where
            (yes _) →
              let c~₁ = ~-ty g₁′~g₂′ (~-ref (~-ty ~ₗ-refl S′~T′))
                  c~₂ = ~-ty g₁~g₂ (~-ref (~-ty ~ₗ-refl S~T)) in
              W ⟨ cast (Ref (S′ of l ℓ₁) of g₁′) (Ref (T′ of l ℓ₁) of g₂′) q c~₁ ⟩
                ⟨ cast (Ref (S of l ℓ₁) of g₁) (Ref (T of l ℓ₁) of g₂) p c~₂ ⟩
            (no _) → error (blame p)


{- NOTE:
   Categorizing by PC, there are two types of _inert_ function casts:
     1) [ pc ] A → B of ℓ₁ ⇒ [ pc ] C → D of g₂
     2) [ pc ] A → B of ℓ₁ ⇒ [ ⋆  ] C → D of g₂
   -}
elim-fun-proxy : ∀ {A B C D gc₁ gc₂ g₁ g₂} {c : Cast ([ gc₁ ] A ⇒ B of g₁) ⇒ ([ gc₂ ] C ⇒ D of g₂)}
  → (V W : Term) → Inert c → (pc : StaticLabel) → Term
elim-fun-proxy V W (I-fun c I-label I-label) pc =
  case c of λ where
  (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ l pc₂ ] C ⇒ D of g₂) p _) →
    (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
  (cast ([ l pc₁ ] A ⇒ B of l ℓ₁) ([ ⋆ ] C ⇒ D of g₂) p _) →
    case (pc ⋎ ℓ₁) ≼? pc₁ of λ where
    (yes _) → cast-pc (l pc) (V · (W ⟨ dom/c c ⟩)) ⟨ cod/c c ⟩
    (no  _) → error (blame p)

elim-ref-proxy : ∀ {A B g₁ g₂} {c : Cast (Ref A of g₁) ⇒ (Ref B of g₂)}
  → (V M : Term) → Inert c → (_⦂=_ : Term → Term → Term) → Term
elim-ref-proxy V M (I-ref c I-label I-label) _⦂=_ =
  case c of λ where
  (cast (Ref (S of (l ℓ₁)) of (l ℓ)) (Ref (T of (l ℓ₂)) of g) p _) →
    V ⦂= (M ⟨ in/c c ⟩)
  (cast (Ref (S of (l ℓ₁)) of (l ℓ)) (Ref (T of ⋆) of g) p _) →
    case ℓ ≼? ℓ₁ of λ where
    (yes _) → V ⦂= (M ⟨ in/c c ⟩)
    (no  _) → error (blame p)


stamp-inert : ∀ {A B} → (c : Cast A ⇒ B) → Inert c → ∀ ℓ
                      → (Cast (stamp A (l ℓ)) ⇒ (stamp B (l ℓ)))
stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι))
            (I-base-inj _) ℓ =
  cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι)
stamp-inert (cast ([ gc₁ ] A ⇒ B of g₁) ([ gc₂ ] C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
            (I-fun _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
    cast ([ gc₁ ] A ⇒ B of (g₁ ⋎̃ l ℓ)) ([ gc₂ ] C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~
stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB))
            (I-ref _ I-label I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
    cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val (addr a of ℓ₁) V-addr ℓ = addr a of (ℓ₁ ⋎ ℓ)
stamp-val (ƛ[ gc ] A ˙ N of ℓ₁) V-ƛ ℓ = ƛ[ gc ] A ˙ N of (ℓ₁ ⋎ ℓ)
stamp-val ($ k of ℓ₁) V-const ℓ = $ k of (ℓ₁ ⋎ ℓ)
stamp-val (V ⟨ c ⟩) (V-cast v i) ℓ = stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩

-- Value stamping is well-typed
stamp-val-wt : ∀ {Γ Σ gc pc V A ℓ}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ A
  → (v : Value V)
  → Γ ; Σ ; gc ; pc ⊢ stamp-val V v ℓ ⦂ stamp A (l ℓ)
stamp-val-wt (⊢addr eq) V-addr = ⊢addr eq
stamp-val-wt (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
stamp-val-wt ⊢const V-const = ⊢const
stamp-val-wt (⊢cast ⊢V) (V-cast v i) = ⊢cast (stamp-val-wt ⊢V v)
stamp-val-wt (⊢sub ⊢V A<:B) v = ⊢sub (stamp-val-wt ⊢V v) (stamp-<: A<:B <:ₗ-refl)
stamp-val-wt (⊢sub-pc ⊢V gc<:gc′) v = ⊢sub-pc (stamp-val-wt ⊢V v) gc<:gc′

-- A stamped value is value
stamp-inert-inert : ∀ {A B} {c : Cast A ⇒ B} {ℓ}
  → (i : Inert c)
  → Inert (stamp-inert c i ℓ)
stamp-inert-inert (I-base-inj c) = I-base-inj _
stamp-inert-inert (I-fun c I-label I-label) =
  I-fun (stamp-inert c _ _) I-label I-label
stamp-inert-inert (I-ref c I-label I-label) =
  I-ref (stamp-inert c _ _) I-label I-label

stamp-val-value : ∀ {V ℓ}
  → (v : Value V)
  → Value (stamp-val V v ℓ)
stamp-val-value V-addr = V-addr
stamp-val-value V-ƛ = V-ƛ
stamp-val-value V-const = V-const
stamp-val-value (V-cast v i) =
  V-cast (stamp-val-value v) (stamp-inert-inert i)

⊢value-pc : ∀ {Σ gc gc′ pc pc′ V A}
  → [] ; Σ ; gc  ; pc ⊢ V ⦂ A
  → Value V
  → [] ; Σ ; gc′ ; pc′ ⊢ V ⦂ A
⊢value-pc (⊢addr eq) V-addr = ⊢addr eq
⊢value-pc (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
⊢value-pc ⊢const V-const = ⊢const
⊢value-pc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-pc ⊢V v)
⊢value-pc (⊢sub ⊢V A<:B) v = ⊢sub (⊢value-pc ⊢V v) A<:B
⊢value-pc (⊢sub-pc ⊢V gc<:gc′) v = ⊢value-pc ⊢V v
