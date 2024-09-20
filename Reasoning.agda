open import Data.Product using (_,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘)
open import Relation.Binary.Construct.Closure.Symmetric using (fwd; bwd)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Definitions
open import Relations

infixr 2 step-⟶ʳ
step-⟶ʳ : ∀ (x : Net i o) {y z}
  → y ⟶* z
  → x ⟶ʳ y
  ----------
  → x ⟶* z
step-⟶ʳ x y⟶*z x⟶ʳy = (_ , ⊘ , x⟶ʳy) ◅ y⟶*z
syntax step-⟶ʳ x y⟶*z x⟶ʳy = x ⟶ʳ⟨ x⟶ʳy ⟩ y⟶*z

infixr 2 step-~-⟶
step-~-⟶ : ∀ (x k : Net i o) {y z}
  → y ⟶* z
  → x ~ k
  → k ⟶ʳ y
  ----------
  → x ⟶* z
step-~-⟶ x _ y⟶*z x~k k⟶ʳy = (_ , x~k , k⟶ʳy) ◅ y⟶*z
syntax step-~-⟶ x k y⟶*z x~k k⟶ʳy = x ~⟨ x~k ⟩ k ⟶⟨ k⟶ʳy ⟩ y⟶*z

_∎ : (n : Net i o) → n ⟶* n
n ∎ = ⊘

module ⟶-examples where
  ε-ε→empty : ε⁺ ⨾ ε⁻ ⟶* id₀
  ε-ε→empty =
    ε⁺ ⨾ ε⁻   ⟶ʳ⟨ ε-ε ⟩
    id₀       ∎

  ε-id-ε→empty : ε⁺ ⨾ id ⨾ ε⁻ ⟶* id₀
  ε-id-ε→empty = 
    ε⁺ ⨾ id ⨾ ε⁻ ~⟨ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    ε⁺ ⨾ ε⁻     ⟶⟨ ε-ε ⟩
    id₀         ∎

  ε-id-ε-id→empty : ε⁺ ⨾ id ⨾ ε⁻ ⨾ id ⟶* id₀
  ε-id-ε-id→empty =
    ε⁺ ⨾ id ⨾ ε⁻ ⨾ id    ~⟨ fwd ⨾-id ◅ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    ε⁺ ⨾ ε⁻             ⟶⟨ ε-ε ⟩
    id₀                 ∎

  δ-id-δ→τ : (δ⁺ ⨾ id ⨾ δ⁻) ⟶* τ
  δ-id-δ→τ =
    δ⁺ ⨾ id ⨾ δ⁻ ~⟨ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    δ⁺ ⨾ δ⁻      ⟶⟨ δ-δ ⟩
    τ            ∎

  δ²⨾δ² : δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻ ⟶* τ ⊗ τ
  δ²⨾δ² =
    δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻     ~⟨ fwd distr ◅ ⊘ ⟩
    (δ⁺ ⨾ δ⁻) ⊗ (δ⁺ ⨾ δ⁻)  ⟶⟨ ⊗₁ δ-δ ⟩
    τ ⊗ (δ⁺ ⨾ δ⁻)          ⟶ʳ⟨ ⊗₂ δ-δ ⟩
    (τ ⊗ τ)                   ∎
