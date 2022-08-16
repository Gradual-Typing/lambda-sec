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
open import CC
open import Reduction
open import HeapTyping


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
ref-wt (Ref-proxy r i sub) = ⊢sub (⊢cast (ref-wt r)) sub

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


{- Plug inversion -}
plug-inversion : ∀ {Σ gc pc M A} {F : Frame}
  → [] ; Σ ; gc ; pc ⊢ plug M F ⦂ A
  → l pc ≾ gc
    -------------------------------------------------------------
  → ∃[ gc′ ] ∃[ B ]
       (l pc ≾ gc′) × ([] ; Σ ; gc′ ; pc ⊢ M ⦂ B) ×
       (∀ {Σ′ M′} → [] ; Σ′ ; gc′ ; pc ⊢ M′ ⦂ B → Σ′ ⊇ Σ → [] ; Σ′ ; gc ; pc ⊢ plug M′ F ⦂ A)
plug-inversion {F = □· M} (⊢app ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢app ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = (V ·□) v} (⊢app ⊢V ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢app (relax-Σ ⊢V Σ′⊇Σ) ⊢M′) ⟩
plug-inversion {F = ref✓[ ℓ ]□} (⊢ref✓ ⊢M pc≼ℓ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢ref✓ ⊢M′ pc≼ℓ) ⟩
plug-inversion {F = !□} (⊢deref ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢deref ⊢M′) ⟩
plug-inversion {F = □:=? M} (⊢assign? ⊢L ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign? ⊢L′ (relax-Σ ⊢M Σ′⊇Σ)) ⟩
plug-inversion {F = □[ ℓ ]:=✓ M} (⊢assign✓ ⊢L ⊢M pc≼ℓ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢assign✓ ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) pc≼ℓ) ⟩
plug-inversion {F = (V [ ℓ ]:=✓□) v} (⊢assign✓ ⊢V ⊢M pc≼ℓ) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢assign✓ (relax-Σ ⊢V Σ′⊇Σ) ⊢M′ pc≼ℓ) ⟩
plug-inversion {F = let□ N} (⊢let ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢let ⊢M′ (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = if□ A M N} (⊢if ⊢L ⊢M ⊢N) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢L , (λ ⊢L′ Σ′⊇Σ → ⊢if ⊢L′ (relax-Σ ⊢M Σ′⊇Σ) (relax-Σ ⊢N Σ′⊇Σ)) ⟩
plug-inversion {F = □⟨ c ⟩} (⊢cast ⊢M) pc≾gc =
  ⟨ _ , _ , pc≾gc , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast ⊢M′) ⟩
plug-inversion {F = cast-pc g □} (⊢cast-pc ⊢M pc~g) _ =
  ⟨ g , _ , proj₁ (~ₗ→≾ pc~g) , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢cast-pc ⊢M′ pc~g) ⟩
plug-inversion (⊢sub ⊢M A<:B) pc≾gc =
  let ⟨ gc′ , B , pc≾gc′ , ⊢M , wt-plug ⟩ = plug-inversion ⊢M pc≾gc in
  ⟨ gc′ , B , pc≾gc′ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub (wt-plug ⊢M′ Σ′⊇Σ) A<:B) ⟩
plug-inversion (⊢sub-pc ⊢plug gc<:gc′) pc≾gc =
  let ⟨ gc″ , B , pc≾gc″ , ⊢M , wt-plug ⟩ = plug-inversion ⊢plug (≾-<: pc≾gc gc<:gc′) in
  ⟨ gc″ , B , pc≾gc″ , ⊢M , (λ ⊢M′ Σ′⊇Σ → ⊢sub-pc (wt-plug ⊢M′ Σ′⊇Σ) gc<:gc′) ⟩


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
