module Compile where

open import Data.Unit using (⊤; tt)

open import SourceLang public
open import TargetLang public


compile : ∀ {Γ pc A} → Γ ; pc ⊢G A → Γ ; ∅ ; pc ⊢ A
compile (` x) = ` x
compile ($ k ^ ℓ) = $ k ^ ℓ
compile (ƛ N ^ ℓ) = ƛ compile N ^ ℓ
compile (prot s M) = prot s (compile M)
compile (_·_at_ {Γ} {pc} {A} {A′} {τᴮ} {ℓᴮ} {pc₀} {ℓ} L M p {cspc} {csl} {cs}) =
  _·_ (compile L) (compile M ⟨ cast A′ A p cs ⟩) {cspc} {csl}
compile (ref s M {cs}) = ref s (compile M) {cs}
compile (L := M) = $ tt ^ ᴸ
compile (! M) = ! compile M
-- This also shows that if Γ ; pc ⊢ M ↪ Mᶜ ⦂ A then Γ ; ∅ ; pc ⊢ Mᶜ ⦂ A
