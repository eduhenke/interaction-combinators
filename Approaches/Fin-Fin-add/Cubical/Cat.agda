open import Prim.Type
open import Data.Nat
open import Data.Fin
open import 1Lab.HLevel.Closure
open import 1Lab.Path
open import Cat.Base hiding (Nat-is-set)
open import Cat.Monoidal.Base
open import Cat.Functor.Subcategory
open import Cat.Functor.WideSubcategory
open import 1Lab.Type renaming (id to id′)
open import 1Lab.Path
open import 1Lab.Type.Pi

open import Data.Sum
-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m + n)
fzero    ↑ˡ n = fzero
(fsuc i) ↑ˡ n = fsuc (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n + m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = fsuc (n ↑ʳ i)

join : ∀ m n → Fin m ⊎ Fin n → Fin (m + n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt _ = split-+

splitAt-↑ˡ : ∀ (m : Nat) (i : Fin m) (n : Nat) → splitAt m (i ↑ˡ n) ≡ inl i
splitAt-↑ˡ _ fzero    _ = refl
splitAt-↑ˡ _ (fsuc i) n = ap (⊎-map fsuc id′) (splitAt-↑ˡ _ i n)

splitAt-↑ʳ : ∀ (m n : Nat) (i : Fin n) → splitAt m (m ↑ʳ i) ≡ inr {B = Fin n} i
splitAt-↑ʳ zero    n i = refl
splitAt-↑ʳ (suc m) n i = ap (⊎-map fsuc id′) (splitAt-↑ʳ m n i)

splitAt-join : ∀ (m n : Nat) (i : Fin m ⊎ Fin n) → splitAt m (join m n i) ≡ i
splitAt-join m n (inl x) = splitAt-↑ˡ m x n
splitAt-join m n (inr y) = splitAt-↑ʳ m n y

Net : Nat → Nat → Type
Net i o = Fin i → Fin o

variable
  i i′ i″ : Nat
  o o′ o″ : Nat
  k k′ k″ : Nat
  f g h : Net i o

infixl 8 _⨾_
_⨾_ : ∀ {i o k : Nat}
  → Net i k
  → Net   k o
  → Net i   o
a ⨾ b = b ∘ a

infixl 9 _⊗_
_⊗_ : ∀ {i₁ i₂ o₁ o₂ : Nat}
  → Net i₁ o₁
  → Net i₂ o₂
  ------------
  → Net (i₁ + i₂) (o₁ + o₂)
_⊗_ {i₁} {i₂} {o₁} {o₂} a b i = let
  i₁⊎i₂ : Fin i₁ ⊎ Fin i₂
  i₁⊎i₂ = splitAt i₁ i
  o₁⊎o₂ : Fin o₁ ⊎ Fin o₂
  o₁⊎o₂ = ⊎-map a b i₁⊎i₂
  o = join o₁ o₂ o₁⊎o₂
  in o

idₛ : i ≡ i′ → Net i i′
idₛ {i} {i′} = subst Fin

id : Net i i
-- id = idₛ refl
id i = i

id₀ = id {0}
{-# DISPLAY id {0} = id₀ #-}

open import 1Lab.Path.IdentitySystem
open import Data.Id.Base

empty-⊗ : id₀ ⊗ f ≡ f
empty-⊗ = refl

splitAt⁻¹-↑ˡᵢ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ᵢ inl j → (j ↑ˡ n) ≡ᵢ i
splitAt⁻¹-↑ˡᵢ {suc m} {n} {fzero} {_} reflᵢ = reflᵢ
splitAt⁻¹-↑ˡᵢ {suc m} {n} {fsuc i} {j} eq
  with inl k ← splitAt m i in eq′
  with reflᵢ ← eq
  = substᵢ (λ x → fsuc (k ↑ˡ n) ≡ᵢ fsuc x) (splitAt⁻¹-↑ˡᵢ {i = i} {j = k} eq′) reflᵢ

splitAt⁻¹-↑ʳᵢ : ∀ {m} {n} {i} {j} → splitAt m {n} i ≡ᵢ inr j → (m ↑ʳ j) ≡ᵢ i
splitAt⁻¹-↑ʳᵢ {zero} {n} {i} {j} reflᵢ = reflᵢ
splitAt⁻¹-↑ʳᵢ {suc m} {n} {fsuc i} {j} eq
  with inr k ← splitAt m i in eq′
  with reflᵢ ← eq
  = substᵢ (λ x → fsuc (m ↑ʳ k) ≡ᵢ fsuc x) (splitAt⁻¹-↑ʳᵢ {i = i} {j = k} eq′) reflᵢ

open import 1Lab.Equiv
id⊗id : ∀ {i i′ : Nat} → id {i} ⊗ id {i′} ≡ id {i + i′}
id⊗id {i} {i′} = funext id⊗id-x
  where
  id⊗id-x : (x : Fin (i + i′)) → (id {i} ⊗ id {i′}) x ≡ id x
  id⊗id-x x with (splitAt i x) in eqnᵢ
  ... | inl fi = Id-identity-system .to-path (splitAt⁻¹-↑ˡᵢ eqnᵢ)
  ... | inr fi′ = Id-identity-system .to-path (splitAt⁻¹-↑ʳᵢ eqnᵢ)

⊗-⨾-distr : ∀ {i o k i′ o′ k′ : Nat}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
⊗-⨾-distr {i} {o} {k} {i′} {o′} {k′} {f₁} {g₁} {f₂} {g₂} = funext ⊗-⨾-distr-x
  where
  ⊗-⨾-distr-x : (x : Fin (i + i′)) → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) x ≡ (f₁ ⊗ f₂ ⨾ g₁ ⊗ g₂) x
  ⊗-⨾-distr-x x with splitAt i x in eq
  ... | inl fi = ap (join o o′ ∘ ⊎-map g₁ g₂) (sym (splitAt-↑ˡ k (f₁ fi) k′))
  ... | inr fi′ = ap (join o o′ ∘ ⊎-map g₁ g₂) (sym (splitAt-↑ʳ k _ (f₂ fi′)))

+0 : ∀ {x : Nat} → x + 0 ≡ x
+0 {x} = +-zeror x

+0′ : ∀ {x : Nat} → x ≡ x + 0
+0′ = sym +0

0+ : ∀ {x : Nat} → 0 + x ≡ x
0+ {x} = refl

⊗-empty : {i o : Nat} {f : Net i o} → f ⊗ id₀ ≡ subst₂ Net +0′ +0′ f
⊗-empty = {!   !}

⨾-idₛ : ∀ {i i′ o o′ : Nat}
  → {i≡ : i ≡ i′}
  → {o≡ : o ≡ o′}
  → {f : Net i o}
  → f ⨾ idₛ o≡ ≡ idₛ i≡ ⨾ subst₂ Net i≡ o≡ f
⨾-idₛ {i≡ = i≡} {o≡ = o≡} = {!   !} -- rewrite i≡ | o≡ = refl

open Precategory hiding (id)

F : Precategory lzero lzero
F .Ob = Nat
F .Hom = Net
F .Hom-set x y = hlevel 2
F .Precategory.id x = x
F .Precategory._∘_ = flip _⨾_
F .idr f = refl
F .idl f = refl
F .assoc f g h = refl

S : Precategory lzero lzero
S = Wide {C = F} (record
  { P = λ{ {x} {y} f → x ≡ y}
  ; P-prop = λ f → Nat-is-set _ _
  ; P-id = refl
  ; P-∘ = λ f g → g ∙ f
  })

open import Cat.Instances.Product
open import 1Lab.Type.Sigma

open import 1Lab.Extensionality

F-Monoidal : Monoidal-category F
F-Monoidal = record
  { -⊗- = Tensor
  ; Unit = 0
  ; unitor-l = record
    { to = NT (λ _ → id) λ _ _ _ → refl
    ; from = NT (λ _ → id) λ _ _ _ → refl
    ; inverses = record { invl = ext (λ _ _ → refl) ; invr = ext (λ _ _ → refl) } }
  ; unitor-r = record
    { to = NT
      (λ x → idₛ (sym (+-zeror x)))
      λ i o f → unitor-r-prop i o f
    ; from = NT
      (λ x → idₛ (+-zeror x))
      λ i o f → {!   !}
    ; inverses = record { invl = ext (λ i x → {!  !}) ; invr = {!   !} } }
  ; associator = record
    { to = NT
      (λ{(x , y , z) → idₛ (sym (+-associative x y z))})
      λ _ _ _ → {!   !}
    ; from = NT
      (λ{(x , y , z) → idₛ (+-associative x y z)})
      λ _ _ _ → {!   !}
    ; inverses = {!   !} }
  ; triangle = {!   !}
  ; pentagon = {!   !}
  }
  
  where
  
  open import Cat.Functor.Base
  open import Cat.Functor.Bifunctor hiding (₁)
  open Functor

  Tensor : Functor (F ×ᶜ F) F
  Tensor .F₀ = uncurry _+_
  Tensor .F₁ = uncurry _⊗_
  Tensor .F-id {i , i′} = id⊗id {i} {i′}
  Tensor .F-∘  _ (g₁ , g₂) = ⊗-⨾-distr {f₁ = g₁} {f₂ = g₂}

  unitor-r-prop : ∀ i o f →
    f ⨾ idₛ +0′ ≡ idₛ +0′ ⨾ (f ⊗ id₀)
  unitor-r-prop i o f =
      ⨾-idₛ {f = f}
    ∙ ap (idₛ +0′ ⨾_) (sym (⊗-empty {f = f}))
