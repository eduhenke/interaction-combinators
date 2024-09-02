open import Categories.Category using (Category)
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.SubCategory using (SubCategory; SubCat)

-- open import Categories.Bicategory using (Bicategory)
-- open import Data.Unit
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Data.Fin.Base using (Fin; join; splitAt)
-- open import Data.List
-- open import Relation.Binary using (IsEquivalence; Setoid)
-- open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_) renaming (id to permutationId)
-- open import Data.Fin.Patterns
-- open import Data.Product using (_×_)
open import Data.Unit
open import Function.Base using (id; _∘_)
open import Agda.Builtin.Sigma 
open import Data.Product using (_×_)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)

-- id, τ
-- Σ = (Σ⁰, Σ¹)
-- Σ⁰ = {(), _⊎_}
-- Σ¹ = {ζ⁺, ε⁺}

F : Category lzero lzero lzero
F = record
  { Obj = ℕ
  ; _⇒_ = λ p q → Fin p → Fin q
  ; _≈_ = _≡_
  ; id = id
  ; _∘_ = λ φ φ' → φ ∘ φ'
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = isEquivalence
  ; ∘-resp-≈ = λ {_} {_} {_} {f} {h} {g} {i} f≡h g≡i →
    begin
      (λ x → f (g x))
    ≡⟨⟩
      f ∘ g
    ≡⟨ Eq.cong (f ∘_) g≡i ⟩
      f ∘ i
    ≡⟨ Eq.cong (_∘ i) f≡h ⟩
      h ∘ i
    ∎
  }

-- F-Monoidal : Monoidal F
-- F-Monoidal = record
--   { ⊗ = record
--     { F₀ = λ{(n₁ , n₂) → n₁ + n₂}
--     ; F₁ = λ{ {A} {B} (φ₁ , φ₂) x →
--       let n₁⊎n₂ = splitAt (fst A) x
--           n₁⊎n₂' = [ inj₁ ∘ φ₁ , inj₂ ∘ φ₂ ]′ n₁⊎n₂
--           n = join _ _ n₁⊎n₂'
--       in n
--     }
--     ; identity = {!   !}
--     ; homomorphism = {!   !}
--     ; F-resp-≈ = λ{(fst₁ , snd₁) → {!   !}}
--     }
--   ; unit = 0
--   ; unitorˡ = {!   !}
--   ; unitorʳ = {!   !}
--   ; associator = {!   !}
--   ; unitorˡ-commute-from = {!   !}
--   ; unitorˡ-commute-to = {!   !}
--   ; unitorʳ-commute-from = {!   !}
--   ; unitorʳ-commute-to = {!   !}
--   ; assoc-commute-from = {!   !}
--   ; assoc-commute-to = {!   !}
--   ; triangle = {!   !}
--   ; pentagon = {!   !}
--   }

-- M-Sub : SubCat F ℕ
-- M-Sub = record
--   { U = id
--   ; R = λ{ {a} {b} φ → Fin a → Fin b}
--   ; Rid = λ x → x
--   ; _∘R_ = λ x x₁ x₂ → x (x₁ x₂) }

-- M : Category lzero lzero lzero
-- M = SubCategory F M-Sub

data MObj : ℕ → ℕ → Set where
  μ : MObj 2 1
  η : MObj 0 1
  pad : ∀ {i o} → MObj i o → MObj 

M : Category lzero lzero lzero
M = record
  { Obj = (Fin 2 → Fin 1) ⊎ (Fin 0 → Fin 1)
  ; _⇒_ = λ x x₁ → {!   !}
  ; _≈_ = {!   !}
  ; id = {!   !}
  ; _∘_ = {!   !}
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = {!   !}
  ; identityʳ = {!   !}
  ; identity² = {!   !}
  ; equiv = {!   !}
  ; ∘-resp-≈ = {!   !}
  }