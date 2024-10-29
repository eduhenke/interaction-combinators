module Net where

open import Data.Nat hiding (_+_)
open import Data.Fin
open import Data.Sum
open import Data.Sum.Properties
open import 1Lab.Type hiding (id; _+_)
open import 1Lab.Path
open import 1Lab.HLevel
open import 1Lab.HLevel.Closure
open import 1Lab.Type.Pi
open import 1Lab.Equiv

data Tree {v} (A : Type v) : Type v where
  # : A → Tree A
  _+_ : Tree A → Tree A → Tree A

Port : Tree Nat → Type
Port (# x) = Fin x
Port (a + b) = Port a ⊎ Port b

Port-is-hlevel : (t : Tree Nat) → is-hlevel (Port t) 2
Port-is-hlevel (# l) = hlevel 2
Port-is-hlevel (a + b) = ⊎-is-hlevel 0 (Port-is-hlevel a) (Port-is-hlevel b)

Net : (i o : Tree Nat) → Type
Net i o = Port i → Port o

Net-is-hlevel : (i o : Tree Nat) → is-hlevel (Net i o) 2
Net-is-hlevel _ o = fun-is-hlevel 2 (Port-is-hlevel o)

variable
  i i′ i″ : Tree Nat
  o o′ o″ : Tree Nat
  k k′ k″ : Tree Nat
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
  → Net (i + i′) (o + o′)
_⊗_ = ⊎-map

id : ∀ {i : Tree Nat} → Net i i
id {i} f = f

id⊗id : ∀ {i i′ : Tree Nat} → id {i} ⊗ id {i′} ≡ id {i + i′}
id⊗id = funext λ{(inl _) → refl; (inr _) → refl}

⊗-⨾-distr : ∀ {i o k i′ o′ k′ : Tree Nat}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
⊗-⨾-distr = funext λ{(inl _) → refl; (inr _) → refl}

open import Cat.Base hiding (Nat-is-set)
open import Cat.Monoidal.Base
open import Cat.Functor.Subcategory
open import Cat.Functor.WideSubcategory

open Precategory hiding (id)

F : Precategory lzero lzero
F .Ob = Tree Nat
F .Hom = Net
F .Hom-set = Net-is-hlevel
F .Precategory.id x = x
F .Precategory._∘_ = flip _⨾_
F .idr f = refl
F .idl f = refl
F .assoc f g h = refl

-- S : Precategory lzero lzero
-- S = Wide {C = F} (record
--   { P = λ{ {x} {y} f → x ≡ y}
--   ; P-prop = λ f → TreeNat-is-hlevel _ _
--   ; P-id = refl
--   ; P-∘ = λ f g → g ∙ f
--   })

open import Cat.Instances.Product
open import 1Lab.Type.Sigma

open import 1Lab.Extensionality

F-Monoidal : Monoidal-category F
F-Monoidal = record
  { -⊗- = record
    { F₀ = uncurry _+_
    ; F₁ = uncurry _⊗_
    ; F-id = λ{ {i , i′} → id⊗id {i} {i′}}
    ; F-∘  = λ _ (g₁ , g₂) → ⊗-⨾-distr {f₁ = g₁} {f₂ = g₂}
    }
  ; Unit = # 0
  ; unitor-l = record
    { to = NT (λ _ → inr) λ _ _ _ → refl
    ; from = NT (λ{_ (inl ()); _ (inr x) → x}) λ{x y f → funext (λ{(inl ()); (inr x) → refl})}
    ; inverses = record { invl = ext λ{_ (inr _) → refl} ; invr = ext (λ{_ _ → refl}) }
    }
  ; unitor-r = record
    { to = NT (λ _ → inl) λ _ _ _ → refl
    ; from = NT (λ{_ (inr ()); _ (inl x) → x}) λ{x y f → funext (λ{(inr ()); (inl x) → refl})}
    ; inverses = record { invl = ext λ{_ (inl _) → refl} ; invr = ext (λ{_ _ → refl}) }
    }
  ; associator = record
    { to = NT
      (λ _ → fst ⊎-assoc)
      λ _ _ _ → funext (λ{(inl (inl x)) → refl ; (inl (inr x)) → refl ; (inr x) → refl})
    ; from = NT
      (λ _ → equiv→inverse (snd ⊎-assoc))
      λ _ _ _ → funext (λ{(inl x) → refl ; (inr (inl x)) → refl ; (inr (inr x)) → refl})
    ; inverses = record
      { invl = ext (λ{_ (inl _) → refl ; _ (inr (inl _)) → refl ; _ (inr (inr _)) → refl})
      ; invr = ext (λ{_ (inl (inl _)) → refl ; _ (inl (inr _)) → refl ; _ (inr _) → refl})
      }
    }
  ; triangle = funext (λ{(inl _) → refl ; (inr (inl ())) ; (inr (inr _)) → refl})
  ; pentagon = funext (λ{(inl _) → refl
                       ; (inr (inl _)) → refl
                       ; (inr (inr (inl _))) → refl
                       ; (inr (inr (inr _))) → refl})
  }
  