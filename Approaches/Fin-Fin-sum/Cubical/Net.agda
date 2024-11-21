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

interchange : ∀ {i o k i′ o′ k′ : Tree Nat}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
interchange = funext λ{(inl _) → refl; (inr _) → refl}

open import Cat.Base hiding (Nat-is-set)
open import Cat.Monoidal.Base
open import Cat.Functor.Subcategory
open import Cat.Functor.WideSubcategory

open Precategory hiding (id; _∘_)

F : Precategory lzero lzero
F .Ob = Tree Nat
F .Hom = Net
F .Hom-set = Net-is-hlevel
F .Precategory.id x = x
F .Precategory._∘_ = flip _⨾_
F .idr f = refl
F .idl f = refl
F .assoc f g h = refl

open import Cat.Instances.Product
open import 1Lab.Type.Sigma

open import 1Lab.Extensionality


F-Monoidal : Monoidal-category F
F-Monoidal = record
  { -⊗- = record
    { F₀ = uncurry _+_
    ; F₁ = uncurry _⊗_ 
    ; F-id = λ{ {i , i′} → id⊗id {i} {i′}}
    ; F-∘  = λ _ (g₁ , g₂) → interchange {f₁ = g₁} {f₂ = g₂}
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

open import Algebra.Ring
open import 1Lab.HLevel.Universe

-- Fin stuff

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m Data.Nat.+ n)
fzero    ↑ˡ n = fzero
(fsuc i) ↑ˡ n = fsuc (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n Data.Nat.+ m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = fsuc (n ↑ʳ i)

join : ∀ m n → Fin m ⊎ Fin n → Fin (m Data.Nat.+ n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]

module Linear {ℓ} (K : Ring ℓ) where

  open import Algebra.Ring.Module public
  open import Algebra.Ring.Module.Vec K public

  open import Algebra.Group.Ab public
  open import Algebra.Group.NAry public
  open import 1Lab.Underlying public

  K^ = Fin-vec-module

  L : Precategory (lsuc ℓ) ℓ
  L = record
    { Ob = Module K ℓ
    ; Hom = Linear-map
    ; Hom-set = λ x y → Linear-map-is-set K {M = x} {N = y}
    ; id = record
      { map = λ x → x
      ; lin = record { linear = λ _ _ _ → refl }
      }
    ; _∘_ = λ f g → record
      { map = f .map ∘ g .map
      ; lin = record { linear = λ r s t → ap (f .map) (g .linear r s t) ∙ f .linear _ _ _ }
      }
    ; idr = λ _ → Linear-map-path λ _ → refl
    ; idl = λ _ → Linear-map-path λ _ → refl
    ; assoc = λ _ _ _ → Linear-map-path λ _ → refl
    }

  canonical-basis : ∀ {T} → Module-on {ℓ} K {ℓ} T → T
  canonical-basis kⁿ = kⁿ .Module-on.has-is-ab .is-abelian-group.1g

  -- this i'm not sure if it is correct
  f₊ : ∀ (m n : Nat) → (f : Net (# m) (# n)) → Linear-map (K^ m) (K^ n)
  f₊ m n f = linear-extension (K^ n) λ xₘ _ → canonical-basis (K^ n .snd) (f xₘ)

  -- this is most definitely correct
  f⁺ : ∀ (m n : Nat) → (f : Net (# m) (# n)) → Linear-map (K^ n) (K^ m)
  f⁺ m n f .map xₙ xₘ = xₙ (f xₘ)
  f⁺ m n f .lin .linear _ _ _ = funext λ _ → refl
  
  _⨾′_ : ∀ {x y z : Module K ℓ} → Linear-map x y → Linear-map y z → Linear-map x z
  a ⨾′ b = L .Precategory._∘_ b a

  _⊕_ : ∀ {x y x′ y′ : Nat}
    → Linear-map (K^ x) (K^ y)
    → Linear-map (K^ x′) (K^ y′)
    → Linear-map (K^ (x Data.Nat.+ x′)) (K^ (y Data.Nat.+ y′))
  _⊕_ {x} {y} {x′} {y′} a b .map x″ fy″ with split-+ {y} fy″
  ... | inl aaa = a .map (x″ ∘ join x x′ ∘ inl) aaa
  ... | inr bbb = b .map (x″ ∘ join x x′ ∘ inr) bbb
  _⊕_ {x} {y} {x′} {y′} a b .lin .linear r s t = funext lin-x≡
    where
    lin-x≡ : (x₁ : Fin (y Data.Nat.+ y′)) →
      map (a ⊕ b)
      ((K^ (x Data.Nat.+ x′) .snd Module-on.+
        (K^ (x Data.Nat.+ x′) .snd Module-on.⋆ r) s)
      t)
      x₁
      ≡
      (K^ (y Data.Nat.+ y′) .snd Module-on.+
      (K^ (y Data.Nat.+ y′) .snd Module-on.⋆ r) (map (a ⊕ b) s))
      (map (a ⊕ b) t) x₁
    lin-x≡ fy″ with split-+ {y} fy″
    ... | inl aaa =
      ap (λ x₁ → x₁ aaa) (a .lin .linear r (s ∘ join x x′ ∘ inl) (t ∘ join x x′ ∘ inl))
    ... | inr bbb =
      ap (λ x₁ → x₁ bbb) (b .lin .linear r (s ∘ join x x′ ∘ inr) (t ∘ join x x′ ∘ inr))

open import IntegerMod2
open Linear ℤ₂-Ring

pattern 0F = fzero
pattern 1F = fsuc fzero

τ : L .Hom (K^ 2) (K^ 2)
τ = linear-extension (K^ 2)
  (λ{0F 0F → 𝕫₀
   ; 0F 1F → 𝕫₁  
   ; 1F 0F → 𝕫₁ 
   ; 1F 1F → 𝕫₀})

δ : L .Hom (K^ 1) (K^ 2)
δ = linear-extension (K^ 2)
  λ{0F 0F → 𝕫₁ 
  ; 0F 1F → 𝕫₁}

ε : L .Hom (K^ 1) (K^ 0)
ε = linear-extension (K^ 0) λ{_ ()}

μ : L .Hom (K^ 2) (K^ 1)
μ = linear-extension (K^ 1)
  λ{0F 0F → 𝕫₁
  ; 1F 0F → 𝕫₁}

η : L .Hom (K^ 0) (K^ 1)
η = linear-extension (K^ 1) λ()

id′ : ∀ {n} → L .Hom (K^ n) (K^ n)
id′ = L .Precategory.id

id₀′ : L .Hom (K^ 0) (K^ 0)
id₀′ = id′ {0}

id₁′ : L .Hom (K^ 1) (K^ 1)
id₁′ = id′ {1}

τ-τ : L .Hom (K^ 2) (K^ 2)
τ-τ = τ ⨾′ τ

open import Data.Vec.Base renaming (map to map-v)
open import Data.Vec.Properties

tabulate-map : ∀ {n m : Nat} {A : Type} (map : (Fin m → A) → (Fin n → A)) → Vec A m → Vec A n
tabulate-map map = tabulate ∘ map ∘ lookup

Linear-map-path-vec-ind :
  ∀ {a b : Nat} {f g : Linear-map (K^ a) (K^ b)}
  → (∀ x → (tabulate-map (f .map) x) ≡ (tabulate-map (g .map) x))
  → f ≡ g
Linear-map-path-vec-ind {f = f} {g = g} eq =
  Linear-map-path (λ x → subst₂ _≡_ (tab-map-simpl f x) (tab-map-simpl g x) (ap lookup (eq (tabulate x)))) --(eq (tabulate x)))
  where
  tab-map-simpl : ∀ {a b : Nat} (m : Linear-map (K^ a) (K^ b))
    → ∀ x → lookup (tabulate-map (m .map) (tabulate x)) ≡ m .map x
  tab-map-simpl {a} {b} m x = funext (λ y →
      lookup-tabulate (m .map (lookup (tabulate x))) y
      ∙ ap (λ z → Linear.map m z y) (funext (lookup-tabulate x))
    )

τ-τ⟶ : τ-τ ≡ id′
τ-τ⟶ = Linear-map-path-vec-ind λ where
  (0F ∷ 0F ∷ []) → refl
  (0F ∷ 1F ∷ []) → refl
  (1F ∷ 0F ∷ []) → refl
  (1F ∷ 1F ∷ []) → refl

μ⨾δ⟶ : μ ⨾′ δ ≡ ((δ ⊕ δ) ⨾′ (((id₁′ ⊕ τ) ⊕ id₁′) ⨾′ (μ ⊕ μ)))
μ⨾δ⟶ = Linear-map-path-vec-ind λ where
  (0F ∷ 0F ∷ []) → refl
  (0F ∷ 1F ∷ []) → refl
  (1F ∷ 0F ∷ []) → refl
  (1F ∷ 1F ∷ []) → refl

η⨾ε⟶ : η ⨾′ ε ≡ id₀′
η⨾ε⟶ = Linear-map-path-vec-ind λ
  [] → refl

η⨾μ⟶ : (η ⊕ id₁′) ⨾′ μ ≡ id₁′
η⨾μ⟶ = Linear-map-path-vec-ind λ where
  (0F ∷ []) → refl
  (1F ∷ []) → refl

δ⨾ε⟶ : δ ⨾′ (ε ⊕ id₁′) ≡ id₁′
δ⨾ε⟶ = Linear-map-path-vec-ind λ where
  (0F ∷ []) → refl
  (1F ∷ []) → refl  