module Values where

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
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_
open import Utils



data Err : Term → Set where
  E-error : ∀ {e : Error} → Err (error e)

data Value : Term → Set where
  V-addr : ∀ {a ℓ} → Value (addr a of ℓ)
  V-ƛ : ∀ {gc A N ℓ} → Value (ƛ[ gc ] A ˙ N of ℓ)
  V-const : ∀ {ι} {k : rep ι} {ℓ} → Value ($ k of ℓ)
  V-cast : ∀ {A B V} {c : Cast A ⇒ B}
    → Value V → Inert c → Value (V ⟨ c ⟩)

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
       (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ A) × (B <: T of ⋆)
canonical⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , ⊢W , <:-ty <:-⋆ <:ᵣ-refl ⟩
canonical⋆ (⊢sub ⊢V (<:-ty {S = T′} <:-⋆ T′<:T)) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , B , c , W , refl , i , ⊢W , B<:T′⋆ ⟩ →
      ⟨ A , B , c , W , refl , i , ⊢W , <:-trans B<:T′⋆ (<:-ty <:-⋆ T′<:T) ⟩
canonical⋆ (⊢sub-pc ⊢V gc<:gc′) v =
  case canonical⋆ ⊢V v of λ where
    ⟨ A , B , c , W , refl , i , ⊢W , B<:T⋆ ⟩ →
      ⟨ A , B , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , B<:T⋆ ⟩

canonical-pc⋆ : ∀ {Γ Σ gc pc V A B g}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ [ ⋆ ] A ⇒ B of g
  → Value V
  → ∃[ C ] ∃[ D ] Σ[ c ∈ Cast C ⇒ D ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ C) × (D <: [ ⋆ ] A ⇒ B of g)
canonical-pc⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , ⊢W , <:-refl ⟩
canonical-pc⋆ (⊢sub ⊢V (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B))) v =
  case canonical-pc⋆ ⊢V v of λ where
    ⟨ C , D , c , W , refl , i , ⊢W , D<:A′→B′ ⟩ →
      let D<:A→B = <:-trans D<:A′→B′ (<:-ty g′<:g (<:-fun <:-⋆ A<:A′ B′<:B)) in
        ⟨ C , D , c , W , refl , i , ⊢W , D<:A→B ⟩
canonical-pc⋆ (⊢sub-pc ⊢V gc<:gc′) v =
  case canonical-pc⋆ ⊢V v of λ where
  ⟨ C , D , c , W , refl , i , ⊢W , D<:A→B ⟩ →
    ⟨ C , D , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , D<:A→B ⟩

canonical-ref⋆ : ∀ {Γ Σ gc pc V T g}
  → Γ ; Σ ; gc ; pc ⊢ V ⦂ Ref (T of ⋆) of g
  → Value V
  → ∃[ A ] ∃[ B ] Σ[ c ∈ Cast A ⇒ B ] ∃[ W ]
       (V ≡ W ⟨ c ⟩) × (Inert c) × (Γ ; Σ ; gc ; pc ⊢ W ⦂ A) × (B <: Ref (T of ⋆) of g)
canonical-ref⋆ (⊢cast ⊢W) (V-cast {V = W} {c} w i) =
  ⟨ _ , _ , c , W , refl , i , ⊢W , <:-refl ⟩
canonical-ref⋆ (⊢sub ⊢V sub) v =
  case sub of λ where
    (<:-ty _ (<:-ref (<:-ty <:-⋆ S<:T) (<:-ty <:-⋆ T<:S))) →
      case canonical-ref⋆ ⊢V v of λ where
        ⟨ A , B , c , W , refl , i , ⊢W , B<:RefS ⟩ →
          ⟨ A , B , c , W , refl , i , ⊢W , <:-trans B<:RefS sub ⟩
canonical-ref⋆ (⊢sub-pc ⊢V gc<:gc′) v =
  case canonical-ref⋆ ⊢V v of λ where
  ⟨ A , B , c , W , refl , i , ⊢W , B<:RefT ⟩ →
    ⟨ A , B , c , W , refl , i , ⊢sub-pc ⊢W gc<:gc′ , B<:RefT ⟩



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
