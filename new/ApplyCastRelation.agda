module ApplyCastRelation where

open import Data.Bool renaming (Bool to 𝔹)
open import Data.Product renaming (_,_ to ⟨_,_⟩)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Function using (case_of_)

open import Utils
open import Types
open import TypeBasedCast
open import CCSyntax Cast_⇒_
open import CCTyping Cast_⇒_
open import Values

infix 4 ApplyCast_,_↝_

data ApplyCast_,_↝_ : ∀ {A B} (V : Term) → (c : Cast A ⇒ B) → Term → Set where

  cast-base-id : ∀ {V ι g} {c : Cast ` ι of g ⇒ ` ι of g}
    → ApplyCast V , c ↝ V

  cast-base-proj : ∀ {V ι ℓ₁ ℓ₂ p q c~ d~}
    → ℓ₁ ≼ ℓ₂
    → let c₁ = cast (` ι of l ℓ₁) (` ι of ⋆) p c~ in
       let c₂ = cast (` ι of ⋆) (` ι of l ℓ₂) q d~ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ V

  cast-base-proj-blame : ∀ {V ι ℓ₁ ℓ₂ p q c~ d~}
    → ¬ ℓ₁ ≼ ℓ₂
    → let c₁ = cast (` ι of l ℓ₁) (` ι of ⋆) p c~ in
       let c₂ = cast (` ι of ⋆) (` ι of l ℓ₂) q d~ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ error (blame q)

  cast-fun-id⋆ : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ gc₁ gc₂ gc₃ gc₄ ℓ p q c~ d~ c~′ d~′}
    → let c₁  = cast ([ gc₁ ] A₁ ⇒ B₁ of l ℓ) ([ gc₂ ] A₂ ⇒ B₂ of ⋆   ) p c~  in
       let c₂  = cast ([ gc₃ ] A₃ ⇒ B₃ of ⋆   ) ([ gc₄ ] A₄ ⇒ B₄ of ⋆   ) q d~  in
       let c₁′ = cast ([ gc₁ ] A₁ ⇒ B₁ of l ℓ) ([ gc₂ ] A₂ ⇒ B₂ of l ℓ) p c~′ in
       let c₂′ = cast ([ gc₃ ] A₃ ⇒ B₃ of l ℓ) ([ gc₄ ] A₄ ⇒ B₄ of ⋆   ) q d~′ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ V ⟨ c₁′ ⟩ ⟨ c₂′ ⟩

  cast-fun-proj : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ gc₁ gc₂ gc₃ gc₄ ℓ₁ ℓ₄ p q c~ d~ c~′ d~′}
    → ℓ₁ ≼ ℓ₄
    → let c₁  = cast ([ gc₁ ] A₁ ⇒ B₁ of l ℓ₁) ([ gc₂ ] A₂ ⇒ B₂ of ⋆   ) p c~  in
       let c₂  = cast ([ gc₃ ] A₃ ⇒ B₃ of ⋆   ) ([ gc₄ ] A₄ ⇒ B₄ of l ℓ₄) q d~  in
       let c₁′ = cast ([ gc₁ ] A₁ ⇒ B₁ of l ℓ₄) ([ gc₂ ] A₂ ⇒ B₂ of l ℓ₄) p c~′ in
       let c₂′ = cast ([ gc₃ ] A₃ ⇒ B₃ of l ℓ₄) ([ gc₄ ] A₄ ⇒ B₄ of l ℓ₄) q d~′ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ V ⟨ c₁′ ⟩ ⟨ c₂′ ⟩

  cast-fun-proj-blame : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ gc₁ gc₂ gc₃ gc₄ ℓ₁ ℓ₄ p q c~ d~}
    → ¬ ℓ₁ ≼ ℓ₄
    → let c₁  = cast ([ gc₁ ] A₁ ⇒ B₁ of l ℓ₁) ([ gc₂ ] A₂ ⇒ B₂ of ⋆   ) p c~  in
       let c₂  = cast ([ gc₃ ] A₃ ⇒ B₃ of ⋆   ) ([ gc₄ ] A₄ ⇒ B₄ of l ℓ₄) q d~  in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ error (blame q)

  cast-fun-pc-id⋆ : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ g₁ g₂ g₃ g₄ pc p q c~ d~ c~′ d~′}
    → let c₁  = cast ([ l pc ] A₁ ⇒ B₁ of g₁) ([ ⋆    ] A₂ ⇒ B₂ of g₂) p c~  in
       let c₂  = cast ([ ⋆    ] A₃ ⇒ B₃ of g₃) ([ ⋆    ] A₄ ⇒ B₄ of g₄) q d~  in
       let c₁′ = cast ([ l pc ] A₁ ⇒ B₁ of g₁) ([ l pc ] A₂ ⇒ B₂ of g₂) p c~′ in
       let c₂′ = cast ([ l pc ] A₃ ⇒ B₃ of g₃) ([ ⋆    ] A₄ ⇒ B₄ of g₄) q d~′ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ V ⟨ c₁′ ⟩ ⟨ c₂′ ⟩

  cast-fun-pc-proj : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ g₁ g₂ g₃ g₄ pc₁ pc₄ p q c~ d~ c~′ d~′}
    → pc₄ ≼ pc₁
    → let c₁  = cast ([ l pc₁ ] A₁ ⇒ B₁ of g₁) ([ ⋆     ] A₂ ⇒ B₂ of g₂) p c~  in
       let c₂  = cast ([ ⋆     ] A₃ ⇒ B₃ of g₃) ([ l pc₄ ] A₄ ⇒ B₄ of g₄) q d~  in
       let c₁′ = cast ([ l pc₄ ] A₁ ⇒ B₁ of g₁) ([ l pc₄ ] A₂ ⇒ B₂ of g₂) p c~′ in
       let c₂′ = cast ([ l pc₄ ] A₃ ⇒ B₃ of g₃) ([ l pc₄ ] A₄ ⇒ B₄ of g₄) q d~′ in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ V ⟨ c₁′ ⟩ ⟨ c₂′ ⟩

  cast-fun-pc-proj-blame : ∀ {V A₁ A₂ A₃ A₄ B₁ B₂ B₃ B₄ g₁ g₂ g₃ g₄ pc₁ pc₄ p q c~ d~}
    → ¬ pc₄ ≼ pc₁
    → let c₁  = cast ([ l pc₁ ] A₁ ⇒ B₁ of g₁) ([ ⋆     ] A₂ ⇒ B₂ of g₂) p c~  in
       let c₂  = cast ([ ⋆     ] A₃ ⇒ B₃ of g₃) ([ l pc₄ ] A₄ ⇒ B₄ of g₄) q d~  in
         ApplyCast V ⟨ c₁ ⟩ , c₂ ↝ error (blame q)


