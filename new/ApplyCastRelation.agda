module ApplyCast where

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

data ApplyCast_,_,_,_≡_ : ∀ {A B} (V : Term) → Value V → (c : Cast A ⇒ B) → Active c → Term → Set where

  cast-base-id : ∀ {V v ι g} {c : Cast ` ι of g ⇒ ` ι of g}
    → ApplyCast V , v , c , A-base-id c ≡ V

  cast-base-proj : ∀ {V v ι ℓ₁ ℓ₂ p q c~ d~}
    → ℓ₁ ≼ ℓ₂
    → let c₁ = cast (` ι of l ℓ₁) (` ι of ⋆) p c~ in
       let c₂ = cast (` ι of ⋆) (` ι of l ℓ₂) q d~ in
         ApplyCast V ⟨ c₁ ⟩ , V-cast v (I-base-inj c₁) , c₂ , A-base-proj c₂ ≡ V

  cast-base-proj-blame : ∀ {V v ι ℓ₁ ℓ₂ p q c~ d~}
    → ¬ ℓ₁ ≼ ℓ₂
    → let c₁ = cast (` ι of l ℓ₁) (` ι of ⋆) p c~ in
       let c₂ = cast (` ι of ⋆) (` ι of l ℓ₂) q d~ in
         ApplyCast V ⟨ c₁ ⟩ , V-cast v (I-base-inj c₁) , c₂ , A-base-proj c₂ ≡ error (blame q)
