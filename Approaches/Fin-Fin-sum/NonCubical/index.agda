module Approaches.Fin-Fin-sum.NonCubical.index where

open import Data.Nat
open import Data.Fin hiding (_+_)
import Data.Sum as Sum
open Sum
open import Data.Sum.Properties
open import Data.Empty
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Function.Base hiding (id)

data Tree {v} (A : Set v) : Set v where
  leaf : A → Tree A
  branch : Tree A → Tree A → Tree A

⊎-tree : Tree ℕ → Set
⊎-tree (leaf x) = Fin x
⊎-tree (branch a b) = ⊎-tree a ⊎ ⊎-tree b

Net : (i o : Tree ℕ) → Set
Net i o = ⊎-tree i → ⊎-tree o
 
variable
  i i′ i″ : Tree ℕ
  o o′ o″ : Tree ℕ
  k k′ k″ : Tree ℕ
  f g h : Net i o

infixl 6 _⨾_
_⨾_ :
    Net i k
  → Net   k o
  → Net i   o
a ⨾ b = λ i → b (a i)

infixl 8 _⊗_
_⊗_ :
    Net i o
  → Net i′ o′
  ------------
  → Net (branch i i′) (branch o o′)
_⊗_ = Sum.map

id : ∀ {i : Tree ℕ} → Net i i
id {i} f = f

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g

id⊗id : ∀ {i i′ : Tree ℕ} → id {i} ⊗ id {i′} ≡ id {branch i i′}
id⊗id = funext [ (λ _ → refl) , (λ _ → refl) ]

⊗-⨾-distr : ∀ {i o k i′ o′ k′ : Tree ℕ}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
⊗-⨾-distr = funext [ (λ _ → refl) , (λ _ → refl) ]

open import Level
open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Product
open import Categories.Functor.Bifunctor

F : Category 0ℓ 0ℓ 0ℓ
F = record
  { Obj = Tree ℕ
  ; _⇒_ = Net
  ; _≈_ = _≡_
  ; id = id
  ; _∘_ = flip _⨾_
  ; assoc = refl
  ; sym-assoc = refl
  ; identityˡ = refl
  ; identityʳ = refl
  ; identity² = refl
  ; equiv = isEquivalence
  ; ∘-resp-≈ = cong₂ (flip _⨾_)
  }

F-Monoidal : Monoidal F
F-Monoidal = monoidalHelper F (record
  { ⊗ = Tensor
  ; unit = leaf 0
  ; unitorˡ = record
    { from = λ{(inj₂ x) → x}
    ; to = inj₂
    ; iso = record { isoˡ = funext (λ{(inj₂ _) → refl}) ; isoʳ = refl } }
  ; unitorʳ = record
    { from = λ{(inj₁ x) → x}
    ; to = inj₁
    ; iso = record { isoˡ = funext (λ{(inj₁ _) → refl}) ; isoʳ = refl } }
  ; associator = record
    { from = Sum.assocʳ
    ; to = Sum.assocˡ
    ; iso = record
      { isoˡ = funext ([ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ])
      ; isoʳ = funext ([ ((λ _ → refl)) , [ (λ _ → refl) , (λ _ → refl) ] ])
      }
    }
  ; unitorˡ-commute = funext (λ{(inj₂ _) → refl})
  ; unitorʳ-commute = funext (λ{(inj₁ _) → refl})
  ; assoc-commute = funext ([ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ])
  ; triangle = funext ([ [ (λ _ → refl) , (λ()) ] , (λ _ → refl) ])
  ; pentagon = funext ([ [ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ] , (λ _ → refl) ])
  })
  where
  open Bifunctor
  Tensor : Bifunctor F F F
  Tensor .F₀ = uncurry branch
  Tensor .F₁ = uncurry _⊗_
  Tensor .identity {i , i′} = id⊗id {i} {i′}
  Tensor .homomorphism {_} {_} {_} {f , _} {g , _} = ⊗-⨾-distr {f₁ = f} {g₁ = g}
  Tensor .F-resp-≈ (f≡g₁ , f≡g₂) rewrite f≡g₁ | f≡g₂ = refl

open import Categories.Category.Monoidal.Symmetric
open import Categories.Category.Monoidal.Braided
open import Categories.NaturalTransformation

F-Braided : Braided F-Monoidal
F-Braided = record
  { braiding = record
    { F⇒G = record
      { η = λ{(a , b) f → Sum.swap f}
      ; commute = λ f → funext ([ (λ _ → refl) , (λ _ → refl) ])
      ; sym-commute = λ f → funext ([ (λ _ → refl) , (λ _ → refl) ])
      }
    ; F⇐G = record
      { η = λ{(a , b) f → Sum.swap f}
      ; commute = λ f → funext ([ (λ _ → refl) , (λ _ → refl) ])
      ; sym-commute = λ f → funext ([ (λ _ → refl) , (λ _ → refl) ])
      }
    ; iso = λ X → record { isoˡ = funext swap-involutive ; isoʳ = funext swap-involutive }
    }
  ; hexagon₁ = funext ([ [ (λ _ → refl) , (λ _ → refl) ] , (λ _ → refl) ])
  ; hexagon₂ = funext ([ ((λ _ → refl)) , [ (λ _ → refl) , (λ _ → refl) ] ])
  }

F-Symmetric : Symmetric F-Monoidal
F-Symmetric = record
  { braided = F-Braided
  ; commutative = funext swap-involutive
  }
 