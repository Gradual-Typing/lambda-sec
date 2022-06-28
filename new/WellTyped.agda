module WellTyped where

open import Data.List hiding ([_])
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Nullary.Negation using (contradiction)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_
open import Values
open import ApplyCast



{- Function and reference predicates respect type -}
fun-wt : ∀ {Σ V gc gc′ pc A B g}
  → Fun V Σ ([ gc′ ] A ⇒ B of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ [ gc′ ] A ⇒ B of g
fun-wt (Fun-ƛ {Σ} ⊢N sub)    = ⊢sub (⊢lam ⊢N) sub
fun-wt (Fun-proxy fun i sub) = ⊢sub (⊢cast (fun-wt fun)) sub

ref-wt : ∀ {Σ V gc pc A g}
  → Reference V Σ (Ref A of g)
  → [] ; Σ ; gc ; pc ⊢ V ⦂ Ref A of g
ref-wt (Ref-addr eq sub)     = ⊢sub (⊢addr eq) sub
ref-wt (Ref-proxy ref i sub) = ⊢sub (⊢cast (ref-wt ref)) sub

{- "Opaque" is not well-typed -}
●-nwt : ∀ {Σ gc pc A} → ¬ ([] ; Σ ; gc ; pc ⊢ ● ⦂ A)
●-nwt {A = ` ι of g} ⊢● =
  case canonical-const ⊢● V-● of λ ()
●-nwt {A = (Ref A) of g} ⊢● =
  case canonical-ref ⊢● V-● of λ ()
●-nwt {A = [ gc ] A ⇒ B of g} ⊢● =
  case canonical-fun ⊢● V-● of λ ()

{- Value stamping is well-typed -}
stamp-val-wt : ∀ {Σ gc pc V A ℓ}
  → [] ; Σ ; gc ; pc ⊢ V ⦂ A
  → (v : Value V)
  → [] ; Σ ; gc ; pc ⊢ stamp-val V v ℓ ⦂ stamp A (l ℓ)
stamp-val-wt (⊢addr eq) V-addr = ⊢addr eq
stamp-val-wt (⊢lam ⊢N) V-ƛ = ⊢lam ⊢N
stamp-val-wt ⊢const V-const = ⊢const
stamp-val-wt (⊢cast ⊢V) (V-cast v i) = ⊢cast (stamp-val-wt ⊢V v)
stamp-val-wt (⊢sub ⊢V A<:B) v = ⊢sub (stamp-val-wt ⊢V v) (stamp-<: A<:B <:ₗ-refl)
stamp-val-wt (⊢sub-pc ⊢V gc<:gc′) v = ⊢sub-pc (stamp-val-wt ⊢V v) gc<:gc′


{- Applying cast is well-typed -}
apply-cast-wt : ∀ {Σ gc pc A B V} {c : Cast A ⇒ B}
  → (⊢V : [] ; Σ ; l low ; low ⊢ V ⦂ A)
  → (v : Value V)
  → (a : Active c)
    -----------------------------------------------------
  → [] ; Σ ; gc ; pc ⊢ apply-cast V ⊢V v c a ⦂ B
apply-cast-wt ⊢V v (A-base-id _) = ⊢value-pc ⊢V v
apply-cast-wt ⊢V v (A-base-proj (cast (` ι of ⋆) (` ι of l ℓ) p (~-ty ⋆~ ~-ι)))
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast (` ι of l ℓ′) (` ι of ⋆) q (~-ty ~⋆ ~-ι) ,
        W , refl , I-base-inj _ , ⊢W , <:-ty <:-⋆ <:-ι ⟩
  with ℓ′ ≼? ℓ
...   | yes ℓ′≼ℓ =
  case v of λ where
  (V-cast w _) → ⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:-ι)
...   | no  _    = ⊢err
apply-cast-wt ⊢V v (A-fun (cast ([ gc₁ ] C₁ ⇒ C₂ of ⋆) ([ gc₂ ] D₁ ⇒ D₂ of g) p (~-ty _ _)) a)
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast ([ gc₁′ ] A₁ ⇒ A₂ of l ℓ′) ([ gc₂′ ] B₁ ⇒ B₂ of ⋆) q (~-ty ~⋆ A~B) ,
        W , refl , I-fun _ I-label I-label , ⊢W , <:-ty <:-⋆ B<:C ⟩
  with a | v
...   | A-id⋆      | V-cast w _ =
  ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl B<:C))
...   | A-proj {ℓ} | V-cast w _
  with ℓ′ ≼? ℓ
...     | yes ℓ′≼ℓ =
  ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl B<:C))
...     | no  _    = ⊢err
apply-cast-wt ⊢V v (A-fun-pc (cast ([ ⋆ ] C₁ ⇒ C₂ of g₁) ([ gc ] D₁ ⇒ D₂ of g₂) p (~-ty g₁~g₂ (~-fun _ C₁~D₁ C₂~D₂))) a I-label)
  with canonical-pc⋆ ⊢V v
... | ⟨ _ , _ , cast ([ l pc′ ] A₁ ⇒ A₂ of g₁′) ([ ⋆ ] B₁ ⇒ B₂ of g₂′) q (~-ty g₁′~g₂′ (~-fun _ A₁~B₁ A₂~B₂)) ,
        W , refl , I-fun _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-fun <:-⋆ C₁<:B₁ B₂<:C₂) ⟩
  with a | v
...   | A-id⋆       | V-cast w _ =
  ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
...   | A-proj {pc} | V-cast w _
  with pc ≼? pc′
...     | yes pc≼pc′ =
  ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty <:ₗ-refl (<:-fun (<:-l pc≼pc′) <:-refl <:-refl))))
              (<:-ty g₂′<:g₁ (<:-fun <:ₗ-refl C₁<:B₁ B₂<:C₂)))
...     | no  _      = ⊢err
apply-cast-wt ⊢V v (A-ref (cast (Ref C of ⋆) (Ref D of g) p (~-ty _ RefC~RefD)) a)
  with canonical⋆ ⊢V v
... | ⟨ _ , _ , cast (Ref A of l ℓ′) (Ref B of ⋆) q (~-ty ~⋆ RefA~RefB) ,
        W , refl , I-ref _ I-label I-label , ⊢W , <:-ty <:-⋆ RefB<:RefC ⟩
  with a | v
...   | A-id⋆      | V-cast w _ =
  ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty <:ₗ-refl RefB<:RefC))
...   | A-proj {ℓ} | V-cast w _
  with ℓ′ ≼? ℓ
...     | yes ℓ′≼ℓ =
  ⊢cast (⊢sub (⊢cast (⊢sub (⊢value-pc ⊢W w) (<:-ty (<:-l ℓ′≼ℓ) <:ᵣ-refl))) (<:-ty <:ₗ-refl RefB<:RefC))
...     | no  _    = ⊢err
apply-cast-wt ⊢V v (A-ref-ref (cast (Ref (S of ⋆) of g₁) (Ref (T of g₂₁) of g₂) p (~-ty g₁~g₂ (~-ref (~-ty _ S~T)))) a I-label)
  with canonical-ref⋆ ⊢V v
... | ⟨ _ , _ , cast (Ref (S′ of l ℓ₁′) of g₁′) (Ref (T′ of ⋆) of g₂′) q (~-ty g₁′~g₂′ (~-ref (~-ty _ S′~T′))) ,
        W , refl , I-ref _ I-label I-label , ⊢W , <:-ty g₂′<:g₁ (<:-ref (<:-ty <:-⋆ T′<:S) (<:-ty <:-⋆ S<:T′)) ⟩
  with a | v
...   | A-id⋆       | V-cast w _ =
  ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′))))
...   | A-proj {ℓ₁} | V-cast w _
  with ℓ₁′ =? ℓ₁
...     | yes refl =
  ⊢cast (⊢sub (⊢cast (⊢value-pc ⊢W w)) (<:-ty g₂′<:g₁ (<:-ref (<:-ty <:ₗ-refl T′<:S) (<:-ty <:ₗ-refl S<:T′))))
...     | no  _    = ⊢err
