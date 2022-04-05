module Utils where

open import Data.List
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import Data.Maybe
open import Data.Nat
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

nth : ∀ {A : Set} → List A → ℕ → Maybe A
nth []       _       = nothing
nth (x ∷ ls) zero    = just x
nth (x ∷ ls) (suc k) = nth ls k

{- Works on association list List (K × V);
   similar to `assoc` in Scheme but has a different
   name because we use "assoc" for associativity.
-}
key : ∀ {K V : Set}
  → (∀ (k₁ k₂ : K) → Dec (k₁ ≡ k₂)) → List (K × V) → K → Maybe V
key _≟_ [] _ = nothing
key _≟_ (⟨ k₀ , v₀ ⟩ ∷ l) k =
  case k ≟ k₀ of λ where
    (yes _) → just v₀
    (no  _) → key _≟_ l k

pattern ⟨_,_,_⟩ x y z = ⟨ x , ⟨ y , z ⟩ ⟩
pattern ⟨_,_,_,_⟩ x y z w = ⟨ x , ⟨ y , ⟨ z , w ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_⟩ x y z w u = ⟨ x , ⟨ y , ⟨ z , ⟨ w , u ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_⟩ x y z w u v = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , v ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_⟩ x y z w u v p = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , p ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
pattern ⟨_,_,_,_,_,_,_,_⟩ x y z w u v p q = ⟨ x , ⟨ y , ⟨ z , ⟨ w , ⟨ u , ⟨ v , ⟨ p , q ⟩ ⟩ ⟩ ⟩ ⟩ ⟩ ⟩
