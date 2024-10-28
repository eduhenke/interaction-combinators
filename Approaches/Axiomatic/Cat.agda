open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘) hiding (gmap)
open import Relation.Binary.Construct.Closure.Symmetric hiding (gmap)
open import Relation.Binary.Construct.Closure.Equivalence using (gmap; isEquivalence; EqClosure)
open import Data.Nat
open import Relation.Binary.PropositionalEquality hiding (isEquivalence)
open Relation.Binary.PropositionalEquality.≡-Reasoning
open import Definitions
open import Relations
open import Function.Base using (flip; case_of_; case_returning_of_)
open import Data.Product using (uncurry; uncurry′; curry′; _,_)
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal
open import Relation.Binary renaming (IsEquivalence to Equiv)

⊗₁* : a ~ b → a ⊗ k ~ b ⊗ k
⊗₁* {k = k} = gmap (_⊗ k) ⊗₁

⊗₂* : a ~ b → k ⊗ a ~ k ⊗ b
⊗₂* {k = k} = gmap (k ⊗_) ⊗₂

⨾₁* : a ~ b → a ⨾ k ~ b ⨾ k
⨾₁* {k = k} = gmap (_⨾ k) ⨾₁

⨾₂* : a ~ b → k ⨾ a ~ k ⨾ b
⨾₂* {k = k} = gmap (k ⨾_) ⨾₂

NetCat : Category 0ℓ 0ℓ 0ℓ
NetCat = record
  { Obj = ℕ
  ; _⇒_ = Net
  ; _≈_ = _~_
  ; id = id
  ; _∘_ = flip _⨾_
  ; assoc = (bwd ⨾-assoc) ◅ ⊘
  ; sym-assoc = (fwd ⨾-assoc) ◅ ⊘
  ; identityˡ = fwd ⨾-id ◅ ⊘
  ; identityʳ = fwd id-⨾ ◅ ⊘
  ; identity² = fwd ⨾-id ◅ ⊘
  ; equiv = isEquivalence _
  ; ∘-resp-≈ = λ a b → ⨾₁* b ◅◅ ⨾₂* a
  }

NetMonoidal : Monoidal NetCat
NetMonoidal = monoidalHelper NetCat (record
  { ⊗ = ⊗-Cat
  ; unit = 0
  ; unitorˡ = {!   !}
  ; unitorʳ = {!   !}
  ; associator = {!   !}
  ; unitorˡ-commute = {!   !}
  ; unitorʳ-commute = {!   !}
  ; assoc-commute = {!   !}
  ; triangle = {!   !}
  ; pentagon = {!   !}
  })
  where
    open Category NetCat renaming (id to idᶜ)
    open import Categories.Functor.Bifunctor using (Bifunctor)
    open import Categories.Morphism NetCat using (_≅_)

    ⊗-Cat : Bifunctor NetCat NetCat NetCat
    ⊗-Cat = record
      { F₀ = uncurry′ _+_
      ; F₁ = uncurry′ _⊗_
      ; identity = fwd id⊗id ◅ ⊘
      ; homomorphism = (bwd distr) ◅ ⊘
      ; F-resp-≈ = uncurry′ λ a b → ⊗₁* a ◅◅ ⊗₂* b 
      }

    unitor : ∀ {X : Obj} → X ≅ X
    unitor {X} = record
      { from = id
      ; to = id
      ; iso = record { isoˡ = fwd ⨾-id ◅ ⊘ ; isoʳ = fwd ⨾-id ◅ ⊘ }
      }
