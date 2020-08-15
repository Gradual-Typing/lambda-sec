open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; ∃; ∃-syntax; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≢_; refl)

open import StaticsGLIO
import Syntax
open Syntax.OpSig Op sig
  using (`_; _⦅_⦆; cons; nil; bind; ast; _[_]; Subst; ⟪_⟫; ⟦_⟧; exts; rename)
  renaming (ABT to Term)
open import Interp
open import Store
open import WellTypedness

{-
  An example:
    let _ = set x y in
      set z w
  where x, y, z, w are free vars (see Γ and γ).
-}
M : Term
M = `let (set (` 0) (` 1)) (set (` 3) (` 4))

Γ : Context
Γ = Ref 𝐻̂ `⊤ ∷ `⊤ ∷ Ref 𝐿̂ `⊤ ∷ `⊤ ∷ []

γ : Env
γ = V-ref ⟨ 0 , 𝐿 , 𝐻 ⟩ ∷ V-tt ∷ V-ref ⟨ 1 , 𝐿 , 𝐿 ⟩ ∷ V-tt ∷ []

μ : Store
μ = ⟨ 0 , 𝐿 , 𝐻 ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷ ⟨ 1 , 𝐿 , 𝐿 ⟩ ↦ ⟨ `⊤ , V-tt ⟩ ∷ []

-- The env is well-typed under Γ, Σ.
⊢γ : Γ ∣ μ ⊢ₑ γ
⊢γ = ⊢ₑ∷ (⊢ᵥref refl) (⊢ₑ∷ ⊢ᵥtt (⊢ₑ∷ (⊢ᵥref refl) (⊢ₑ∷ ⊢ᵥtt ⊢ₑ∅)))

-- The heap is well-typed under Σ.
⊢μ : μ ⊢ₛ μ
⊢μ = ⊢ₛ∷ ⊢ᵥtt (⊢ₛ∷ ⊢ᵥtt ⊢ₛ∅)

-- The term with double heap assignments is well-typed under Γ.
⊢M : Γ [ 𝐿̂ , 𝐿̂ ]⊢ M ⦂ `⊤
⊢M = ⊢let (⊢set refl refl ≲-⊤ (≾-l (≼-l z≤n))) (⊢set refl refl ≲-⊤ (≾-l (≼-l z≤n))) ≲-⊤

-- Even if the term M is accepted by the type checker, it errors at runtime by throwing an NSUError.
run : 𝒱 γ M ⊢M μ 𝐿 10 ≡ error NSUError
run = refl
