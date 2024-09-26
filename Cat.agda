open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘) hiding (gmap)
open import Relation.Binary.Construct.Closure.Symmetric hiding (gmap)
open import Relation.Binary.Construct.Closure.Equivalence using (gmap; isEquivalence; EqClosure)
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-identityˡ; +-identityʳ; +-assoc)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning
open import Definitions
open import Relations
open import Function.Base using (flip; case_of_; case_returning_of_)
open import Data.Product using (uncurry; uncurry′; curry′; _,_)
open import Categories.Category
open import Categories.Category.Product
open import Categories.Category.Monoidal using (Monoidal; monoidalHelper)
open import Relation.Binary using (IsEquivalence)

⊗₁* : a ~ b → a ⊗ k ~ b ⊗ k
⊗₁* {k = k} = gmap (_⊗ k) ⊗₁

⊗₂* : a ~ b → k ⊗ a ~ k ⊗ b
⊗₂* {k = k} = gmap (k ⊗_) ⊗₂

⨾₁* : a ~ b → a ⨾ k ~ b ⨾ k
⨾₁* {k = k} = gmap (_⨾ k) ⨾₁

⨾₂* : a ~ b → k ⨾ a ~ k ⨾ b
⨾₂* {k = k} = gmap (k ⨾_) ⨾₂

⨾-Cat : Category 0ℓ 0ℓ 0ℓ
⨾-Cat = record
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

⨾-Monoidal : Monoidal ⨾-Cat
⨾-Monoidal = monoidalHelper ⨾-Cat (record
  { ⊗ = ⊗-Cat
  ; unit = 0
  ; unitorˡ = unitorˡ
  ; unitorʳ = unitorʳ
  ; associator = λ {X} {Y} {Z} → associator {X} {Y} {Z}
  ; unitorˡ-commute = unitorˡ-commute
  ; unitorʳ-commute = λ {i} {o} {f} → unitorʳ-commute {i} {o} {f}
  ; assoc-commute = λ{ {f = f} {g = g} {h = h} → assoc-commute {f = f} {g = g} {h = h} }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  })
  where
    open Category ⨾-Cat renaming (id to idᶜ)
    open import Categories.Functor.Bifunctor using (Bifunctor)
    open import Categories.Morphism ⨾-Cat using (_≅_)
    
    variable
      X Y Z : Obj

    ⊗-Cat : Bifunctor ⨾-Cat ⨾-Cat ⨾-Cat
    ⊗-Cat = record
      { F₀ = uncurry′ _+_
      ; F₁ = uncurry′ _⊗_
      ; identity = fwd id⊗id ◅ ⊘
      ; homomorphism = (bwd distr) ◅ ⊘
      ; F-resp-≈ = uncurry′ λ a b → ⊗₁* a ◅◅ ⊗₂* b 
      }

    open Bifunctor ⊗-Cat

    unitorˡ : 0 + X ≅ X
    unitorˡ {X} = record
      { from = id₀ ⊗ X′
      ; to = X′ ⊗ id₀
      ; iso = record
        { isoˡ = fwd (⨾₁ id⊗id) ◅ fwd (⨾₂ ⊗-empty) ◅ fwd id-⨾ ◅ ⊘
        ; isoʳ = fwd (⨾₁ ⊗-empty) ◅ fwd id-⨾ ◅ fwd id⊗id ◅ ⊘ }
      }
      where X′ = id {X}

    unitorʳ : ∀ {X : ℕ} → X + 0 ≅ X
    unitorʳ {X}
      -- rewriting needed because X+0 doesn't simplify as nicely as 0+X above
      rewrite (+-identityʳ X)
      =
        record
          { from = X′ ⊗ id₀
          ; to = id₀ ⊗ X′
          ; iso = record
            { isoˡ = fwd (⨾₁ ⊗-empty) ◅ fwd id-⨾ ◅ fwd id⊗id ◅ ⊘
            ; isoʳ = fwd (⨾₁ id⊗id) ◅ fwd (⨾₂ ⊗-empty) ◅ fwd id-⨾ ◅ ⊘ }
          }
      where
        X′ = id {X}

    associator : (X + Y) + Z ≅ X + (Y + Z)
    associator {X} {Y} {Z}
      rewrite (+-assoc X Y Z)
      = record
      { from = X′ ⊗ (Y′ ⊗ Z′)
      ; to = X′ ⊗ (Y′ ⊗ Z′)
      ; iso = record { isoˡ = iso ; isoʳ = iso } }
      where
        X′ = id {X}
        Y′ = id {Y}
        Z′ = id {Z}
        iso : X′ ⊗ (Y′ ⊗ Z′) ⨾ X′ ⊗ (Y′ ⊗ Z′) ~ id
        iso = fwd (⨾₁ (⊗₂ id⊗id))
            ◅ fwd (⨾₁ id⊗id)
            ◅ fwd id-⨾
            ◅ fwd (⊗₂ id⊗id)
            ◅ fwd id⊗id
            ◅ ⊘
    
  --unitorˡ-commute : ∀ {f : Net i o} → (id₀ ⊗ f) ⨾ unitorˡ.from   ~ unitorˡ.from   ⨾ f
    unitorˡ-commute : ∀ {f : Net i o} → (id₀ ⊗ f) ⨾ (id₀ ⊗ id {o}) ~ (id₀ ⊗ id {i}) ⨾ f
    unitorˡ-commute =
        fwd (⨾₁ empty-⊗)
      ◅ fwd (⨾₂ empty-⊗)
      ◅ fwd ⨾-id
      ◅ bwd id-⨾
      ◅ bwd (⨾₁ empty-⊗)
      ◅ ⊘
    
    unitorʳ-commute : ∀ {f : Net i o} → f ⊗ id₀ ⨾ _≅_.from (unitorʳ {o}) ~ _≅_.from (unitorʳ {i}) ⨾ f
  --unitorʳ-commute : ∀ {f : Net i o} → f ⊗ id₀ ⨾ (id {o} ⊗ id₀) ~ (id {i} ⊗ id₀) ⨾ f
    unitorʳ-commute {i} {o} {f} = {!   !}
    -- unitorʳ-commute {i} {o} {f} rewrite (+-identityʳ i) = {!   !}
    -- case (+-identityʳ i)  of λ{x → fwd (⨾₁ {! ⊗-empty {?} {?} {?}  !}) ◅ {!   !} ◅ ⊘}
    --   Eq.subst (λ x → (_~_ {x} {o}) (_⊗_ {{_}} f id₀ ⨾ _≅_.from (unitorʳ {o})) _) (Eq.sym (+-identityʳ i))
    --   (Eq.subst (λ x → (_~_ {_} {x}) _ _) ( (+-identityʳ o))
    --     ({!   !} ◅ ⊘))
    --   -- fwd (⨾₁ (Eq.subst _ (+-identityʳ i) ⊗-empty)) ◅ fwd (⨾₂ (Eq.subst _ (+-identityʳ o) ⊗-empty)) ◅ fwd {! ⨾-id  !} ◅ {!   !} ◅ ⊘

    -- asd : (x : ℕ) → _≅_.from (unitorʳ {x}) ≡ ((id {x}) ⊗ id₀)
    -- asd x =
    --   let
    --     bla : Net (x + 0) x
    --     bla = _≅_.from (unitorʳ {x})
    --     blo : Net x x
    --     blo = bloo bla
    --     -- b≡b : bla ≡ blo
    --     -- b≡b = ?
    --   in begin
    --     (_≅_.from {x + 0} {x}) (unitorʳ {x}) ≡⟨⟩
    --     {! _⊗_ {i = x + 0} {o = x} {i₁ = x} {i₂ = 0} {o₁ = x} {o₂ = 0} {{?}} {{?}} id id₀ !}  ≡⟨ {!   !} ⟩
    --     {! bla !} ∎
    --   where
    --     bloo : Net (x + 0) x → Net x x
    --     bloo n rewrite (+-identityʳ x) = n 
    

    assoc-commute : ∀ {f : Net i₁ o₁} {g : Net i₂ o₂} {h : Net i₃ o₃} →
      F₁ (F₁ (f , g) , h) ⨾ _≅_.from (associator {o₁} {o₂} {o₃}) ≈
      _≅_.from (associator {i₁} {i₂} {i₃}) ⨾ (F₁ (f , F₁ (g , h)))
    assoc-commute = {!   !} 