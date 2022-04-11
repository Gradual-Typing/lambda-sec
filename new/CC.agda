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

data Boolean : Term → Set where
  Bool-true  : ∀ {ℓ} → Boolean ($ true of ℓ)
  Bool-false : ∀ {ℓ} → Boolean ($ false of ℓ)
  Bool-cast : ∀ {b : 𝔹} {g ℓ} {c : Cast (` Bool of g) ⇒ (` Bool of ⋆)}
    → Inert c
    → Boolean ($ b of ℓ ⟨ c ⟩)

canonical-fun : ∀ {Γ Σ gc gc′ A B g V}
  → Γ ; Σ ; gc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
  → Value V
  → Fun V
canonical-fun (⊢lam _) V-ƛ = Fun-ƛ
canonical-fun (⊢cast _) (V-cast v (I-fun c i)) = Fun-proxy v (I-fun c i)
canonical-fun (⊢sub ⊢V (<:-ty _ (<:-fun _ _ _))) v = canonical-fun ⊢V v
canonical-fun (⊢sub-gc ⊢V gc<:gc′) v = canonical-fun ⊢V v

canonical-ref : ∀ {Γ Σ gc A g V}
  → Γ ; Σ ; gc ⊢ V ⦂ Ref A of g
  → Value V
  → Refer V
canonical-ref (⊢addr _) V-addr = Ref-addr
canonical-ref (⊢cast _) (V-cast v (I-ref c i)) = Ref-proxy v (I-ref c i)
canonical-ref (⊢sub ⊢V (<:-ty _ (<:-ref _ _))) v = canonical-ref ⊢V v
canonical-ref (⊢sub-gc ⊢V gc<:gc′) v = canonical-ref ⊢V v

canonical⋆ : ∀ {Γ Σ gc V T}
  → Γ ; Σ ; gc ⊢ V ⦂ T of ⋆
  → Value V
  → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ] (V ≡ W ⟨ c ⟩) × (Inert c) × (B <: T of ⋆)
canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) = ⟨ _ , _ , ⟨ c , W , refl , i , <:-ty <:-⋆ <:ᵣ-refl ⟩ ⟩
canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , B , ⟨ c , W , refl , i , B<:T′⋆ ⟩ ⟩ →
      ⟨ A , B , ⟨ c , W , refl , i , <:-trans B<:T′⋆ (<:-ty <:-⋆ T′<:T) ⟩ ⟩
canonical⋆ (⊢sub-gc ⊢V gc<:gc′) v = canonical⋆ ⊢V v

private
  canonical-const-const : ∀ {Γ Σ gc ι ℓ V}
    → Γ ; Σ ; gc ⊢ V ⦂ ` ι of l ℓ
    → Value V
    → Σ[ k ∈ rep ι ] ∃[ ℓ′ ] V ≡ $ k of ℓ′
  canonical-const-const ⊢const V-const = ⟨ _ , _ , refl ⟩
  canonical-const-const (⊢sub ⊢V (<:-ty (<:-l _) <:-ι)) v = canonical-const-const ⊢V v
  canonical-const-const (⊢sub-gc ⊢V gc<:gc′) v = canonical-const-const ⊢V v
  canonical-const-cast : ∀ {Γ Σ gc ι V}
    → Γ ; Σ ; gc ⊢ V ⦂ ` ι of ⋆
    → Value V
    → Σ[ k ∈ rep ι ] ∃[ ℓ ] ∃[ ℓ′ ] Σ[ c ∈ Cast (` ι of l ℓ) ⇒ (` ι of ⋆) ] V ≡ $ k of ℓ′ ⟨ c ⟩
  canonical-const-cast (⊢cast ⊢V) (V-cast v (I-base-inj _)) =
    case canonical-const-const ⊢V v of λ where
      ⟨ k , ℓ′ , refl ⟩ → ⟨ k , ⟨ _ , ⟨ ℓ′ , ⟨ _ , refl ⟩ ⟩ ⟩ ⟩
  canonical-const-cast (⊢sub ⊢V (<:-ty <:-⋆ <:-ι)) v = canonical-const-cast ⊢V v
  canonical-const-cast (⊢sub-gc ⊢V gc<:gc′) v = canonical-const-cast ⊢V v
canonical-bool : ∀ {Γ Σ gc g V}
  → Γ ; Σ ; gc ⊢ V ⦂ ` Bool of g
  → Value V
  → Boolean V
canonical-bool {g = ⋆} ⊢V v =
  case canonical-const-cast ⊢V v of λ where
    ⟨ k  , ℓ , ℓ′ , c , refl ⟩ → Bool-cast (I-base-inj c)
canonical-bool {g = l ℓ} ⊢V v =
  case canonical-const-const ⊢V v of λ where
    ⟨ true  , ℓ′ , refl ⟩ → Bool-true
    ⟨ false , ℓ′ , refl ⟩ → Bool-false

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
unwrap (V ⟨ c ⟩) (V-cast v i) = unwrap V v
unwrap V _ = V

unwrap-ref : ∀ {Γ Σ gc V A g}
  → Γ ; Σ ; gc ⊢ V ⦂ Ref A of g
  → (v : Value V)
  → ∃[ a ] ∃[ ℓ ] (unwrap V v ≡ addr a of ℓ) × (∃[ A′ ] Γ ; Σ ; gc ⊢ addr a of ℓ ⦂ Ref A′ of l ℓ)
unwrap-ref (⊢addr eq) V-addr = ⟨ _ , _ , refl , _ , ⊢addr eq ⟩
unwrap-ref (⊢cast ⊢V) (V-cast {c = cast A B _ (~-ty _ (~-ref _))} v i) =
  unwrap-ref ⊢V v
unwrap-ref (⊢sub ⊢V (<:-ty _ (<:-ref A<:B B<:A))) v
  rewrite <:-antisym A<:B B<:A = unwrap-ref ⊢V v
unwrap-ref (⊢sub-gc ⊢V gc<:gc′) v =
  let ⟨ a , ℓ , eq , A′ , ⊢a ⟩ = unwrap-ref ⊢V v in
    ⟨ a , ℓ , eq , A′ , ⊢sub-gc ⊢a gc<:gc′ ⟩

stamp-inert : ∀ {A B} → (c : Cast A ⇒ B) → Inert c → ∀ ℓ
                      → (Cast (stamp A (l ℓ)) ⇒ (stamp B (l ℓ)))
stamp-inert (cast (` ι of l ℓ₁) (` ι of ⋆) p (~-ty ~⋆ ~-ι))
            (I-base-inj _) ℓ =
  cast (` ι of l (ℓ₁ ⋎ ℓ)) (` ι of ⋆) p (~-ty ~⋆ ~-ι)
stamp-inert (cast ([ gc₁ ] A ⇒ B of g₁) ([ gc₂ ] C ⇒ D of g₂) p (~-ty g₁~g₂ A→B~C→D))
            (I-fun _ I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) A→B~C→D in
    cast ([ gc₁ ] A ⇒ B of (g₁ ⋎̃ l ℓ)) ([ gc₂ ] C ⇒ D of (g₂ ⋎̃ l ℓ)) p c~
stamp-inert (cast (Ref A of g₁) (Ref B of g₂) p (~-ty g₁~g₂ RefA~RefB))
            (I-ref _ I-label) ℓ =
  let c~ = ~-ty (consis-join-~ₗ g₁~g₂ ~ₗ-refl) RefA~RefB in
    cast (Ref A of (g₁ ⋎̃ l ℓ)) (Ref B of (g₂ ⋎̃ l ℓ)) p c~

stamp-val : ∀ V → Value V → StaticLabel → Term
stamp-val (addr a of ℓ₁) V-addr ℓ = addr a of (ℓ₁ ⋎ ℓ)
stamp-val (ƛ[ gc ] A ˙ N of ℓ₁) V-ƛ ℓ = ƛ[ gc ] A ˙ N of (ℓ₁ ⋎ ℓ)
stamp-val ($ k of ℓ₁) V-const ℓ = $ k of (ℓ₁ ⋎ ℓ)
stamp-val (V ⟨ c ⟩) (V-cast v i) ℓ = stamp-val V v ℓ ⟨ stamp-inert c i ℓ ⟩

-- Value stamping is well-typed
stamp-val-wt : ∀ {Γ Σ gc V A ℓ}
  → Γ ; Σ ; gc ⊢ V ⦂ A
  → (v : Value V)
  → Γ ; Σ ; gc ⊢ stamp-val V v ℓ ⦂ stamp A (l ℓ)
stamp-val-wt (⊢addr eq) V-addr = ⊢addr eq
stamp-val-wt (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
stamp-val-wt ⊢const V-const = ⊢const
stamp-val-wt (⊢cast ⊢V) (V-cast v i) = ⊢cast (stamp-val-wt ⊢V v)
stamp-val-wt (⊢sub ⊢V A<:B) v = ⊢sub (stamp-val-wt ⊢V v) (stamp-<: A<:B <:ₗ-refl)
stamp-val-wt (⊢sub-gc ⊢V gc<:gc′) v = ⊢sub-gc (stamp-val-wt ⊢V v) gc<:gc′

-- A stamped value is value
stamp-inert-inert : ∀ {A B} {c : Cast A ⇒ B} {ℓ}
  → (i : Inert c)
  → Inert (stamp-inert c i ℓ)
stamp-inert-inert (I-base-inj c) = I-base-inj _
stamp-inert-inert (I-fun c I-label) = I-fun (stamp-inert c _ _) I-label
stamp-inert-inert (I-ref c I-label) = I-ref (stamp-inert c _ _) I-label

stamp-val-value : ∀ {V ℓ}
  → (v : Value V)
  → Value (stamp-val V v ℓ)
stamp-val-value V-addr = V-addr
stamp-val-value V-ƛ = V-ƛ
stamp-val-value V-const = V-const
stamp-val-value (V-cast v i) = V-cast (stamp-val-value v) (stamp-inert-inert i)

⊢value-gc : ∀ {Σ gc gc′ V A}
  → [] ; Σ ; gc ⊢ V ⦂ A
  → Value V
  → [] ; Σ ; gc′ ⊢ V ⦂ A
⊢value-gc (⊢addr eq) V-addr = ⊢addr eq
⊢value-gc (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
⊢value-gc ⊢const V-const = ⊢const
⊢value-gc (⊢cast ⊢V) (V-cast v i) = ⊢cast (⊢value-gc ⊢V v)
⊢value-gc (⊢sub ⊢V A<:B) v = ⊢sub (⊢value-gc ⊢V v) A<:B
⊢value-gc (⊢sub-gc ⊢V gc<:gc′) v = ⊢value-gc ⊢V v

-- If an address is well-typed, the heap context lookup is successful.
⊢addr-lookup : ∀ {Γ Σ gc a ℓ A g}
  → Γ ; Σ ; gc ⊢ addr a of ℓ ⦂ Ref A of g
  → key _≟_ Σ a ≡ just A
⊢addr-lookup (⊢addr eq) = eq
⊢addr-lookup (⊢sub ⊢a (<:-ty _ (<:-ref A<:B B<:A)))
  rewrite <:-antisym A<:B B<:A = ⊢addr-lookup ⊢a
⊢addr-lookup (⊢sub-gc ⊢a gc<:gc′) = ⊢addr-lookup ⊢a

-- The labels on a constant and its type are related by subtyping.
const-label : ∀ {Γ Σ gc ι} {k : rep ι} {ℓ g}
  → Γ ; Σ ; gc ⊢ $ k of ℓ ⦂ ` ι of g
  → ∃[ ℓ′ ] (g ≡ l ℓ′) × (ℓ ≼ ℓ′)
const-label {ℓ = ℓ} ⊢const = ⟨ ℓ , refl , ≼-refl ⟩
const-label (⊢sub ⊢M (<:-ty ℓ′<:g <:-ι)) =
  case ⟨ const-label ⊢M , ℓ′<:g ⟩ of λ where
    ⟨ ⟨ ℓ′ , refl , ℓ≼ℓ′ ⟩ , <:-l ℓ′≼ℓ″ ⟩ →
      ⟨ _ , refl , ≼-trans ℓ≼ℓ′ ℓ′≼ℓ″ ⟩
const-label (⊢sub-gc ⊢M gc<:gc′) = const-label ⊢M
