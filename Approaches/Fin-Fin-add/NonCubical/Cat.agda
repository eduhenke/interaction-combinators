open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin hiding (_+_)
open import Data.Fin.Properties
open import Data.Sum renaming (map to ⊎-map)
open import Data.Product
open import Function.Base hiding (id)
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Binary.PropositionalEquality.Properties
open ≡-Reasoning

Net : ℕ → ℕ → Set
Net i o = Fin i → Fin o

variable
  i i′ i″ : ℕ
  o o′ o″ : ℕ
  k k′ k″ : ℕ
  f g h : Net i o

infixl 6 _⨾_
_⨾_ :
    Net i k
  → Net   k o
  → Net i   o
a ⨾ b = λ f → b (a f)

infixl 8 _⊗_
_⊗_ :
    Net i o
  → Net i′ o′
  ------------
  → Net (i + i′) (o + o′)
_⊗_ {i₁} {o₁} {i₂} {o₂} a b f = let
  i₁⊎i₂ : Fin i₁ ⊎ Fin i₂
  i₁⊎i₂ = splitAt i₁ f
  o₁⊎o₂ : Fin o₁ ⊎ Fin o₂
  o₁⊎o₂ = Data.Sum.map a b i₁⊎i₂
  o = join o₁ o₂ o₁⊎o₂
  in o

idₛ : i ≡ i′ → Net i i′
idₛ {i} {i′} = subst Fin

id : Net i i
id = idₛ refl

id₀ = id {0}
{-# DISPLAY id {0} = id₀ #-}

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g

substₙ :
    i ≡ i′
  → o ≡ o′
  → Net i o
  → Net i′ o′
substₙ i≡ o≡ = subst₂ Net i≡ o≡

substₙ-app :
    (i≡ : i ≡ i′)
  → (o≡ : o ≡ o′)
  → (f : Net i o)
  → (x : Fin i′)
  → (substₙ i≡ o≡ f) x ≡ subst Fin o≡ (f (subst Fin (sym i≡) x))
substₙ-app refl refl f x = refl

+0 : ∀ {x : ℕ} → x + 0 ≡ x
+0 {x} = +-identityʳ x

+0′ : ∀ {x : ℕ} → x ≡ x + 0
+0′ = sym +0

0+ : ∀ {x : ℕ} → 0 + x ≡ x
0+ {x} = +-identityˡ x

empty-⊗ : id₀ ⊗ f ≡ f
empty-⊗ = refl

⊗-empty : f ⊗ id₀ ≡ substₙ +0′ +0′ f
⊗-empty {i} {o} {f} = funext ⊗-empty-x
  where
  ⊗-empty-x : (x : Fin (i + 0)) → (f ⊗ id₀) x ≡ substₙ +0′ +0′ f x
  ⊗-empty-x x with splitAt i x in eq
  ... | inj₁ fi =
    begin
      (f fi) ↑ˡ 0  
    ≡⟨ asd ⟩
      subst Fin +0′ (f fi)
    ≡⟨ cong (λ x₁ → subst Fin +0′ (f x₁)) {!  !} ⟩
      subst Fin +0′ (f (subst Fin (sym +0′) x))
    ≡⟨ sym (substₙ-app +0′ +0′ f x) ⟩
      substₙ +0′ +0′ f x
    ∎
    where
      asd : ∀ {x} → x ↑ˡ 0 ≡ subst Fin +0′ x
      asd {zero} = {! refl  !}
      asd {suc x} = {!   !}

  ... | inj₂ ()

id⊗id : id {i} ⊗ id {i′} ≡ id {i + i′}
id⊗id {i} {i′} = funext id⊗id-x
  where
  id⊗id-x : (x : Fin (i + i′)) → (id {i} ⊗ id {i′}) x ≡ id x
  id⊗id-x x with splitAt i x in eq
  ... | inj₁ fi = splitAt⁻¹-↑ˡ eq
  ... | inj₂ fi′ = splitAt⁻¹-↑ʳ eq

⊗-⨾-distr : ∀ {i o k i′ o′ k′ : ℕ}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
⊗-⨾-distr {i} {o} {k} {i′} {o′} {k′} {f₁} {g₁} {f₂} {g₂} = funext ⊗-⨾-distr-x
  where
  ⊗-⨾-distr-x : (x : Fin (i + i′)) → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) x ≡ (f₁ ⊗ f₂ ⨾ g₁ ⊗ g₂) x
  ⊗-⨾-distr-x x with splitAt i x in eq
  ... | inj₁ fi rewrite splitAt-↑ˡ k (f₁ fi) k′ = refl
  ... | inj₂ fi′ rewrite splitAt-↑ʳ k _ (f₂ fi′) = refl


subst-sym-sym : {A : Set} {x y : A} {P : A → Set} (x≡y : x ≡ y) {p : P x} →
                  subst P (sym (sym x≡y)) p ≡ subst P x≡y p 
subst-sym-sym refl = refl

⊗-assoc : {i o : ℕ} {f : Net i o} {i′ o′ : ℕ} {g : Net i′ o′} {i″ o″ : ℕ} {h : Net i″ o″}
  → (f ⊗ g) ⊗ h ≡ substₙ (sym (+-assoc i i′ i″)) ((sym (+-assoc o o′ o″))) (f ⊗ (g ⊗ h))
⊗-assoc {i} {o} {f} {i′} {o′} {g} {i″} {o″} {h} = funext ⊗-assoc-x
  where
  assocⁱ = +-assoc i i′ i″
  assocᵒ = +-assoc o o′ o″
  ⊗-assoc-x : (x : Fin (i + i′ + i″)) → (f ⊗ g ⊗ h) x ≡ substₙ (sym assocⁱ) (sym assocᵒ) (f ⊗ (g ⊗ h)) x
  ⊗-assoc-x x with splitAt (i + i′) x in eq
  ... | inj₁ fii′ with splitAt i fii′ in eq′
  ...           | inj₁ fi =
                  sym (trans
                    {!   !}
                    {!   !})
  ...           | inj₂ fi′ = splitAt⁻¹-↑ˡ {!   !} 
  ⊗-assoc-x x | inj₂ fi″ = sym (begin
    substₙ (sym assocⁱ) (sym assocᵒ)
      (join o (o′ + o″)
      ∘ ⊎-map f (join o′ o″ ∘ ⊎-map g h ∘ splitAt i′)
      ∘ splitAt i)
      x ≡⟨ {!   !} ⟩
    {!   !}
    )


open import Level
open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Category.Product
open import Categories.Functor.Bifunctor

F : Category 0ℓ 0ℓ 0ℓ
F = record
  { Obj = ℕ
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

⨾-idₛ : ∀ {i i′ o o′ : ℕ}
  → {i≡ : i ≡ i′}
  → {o≡ : o ≡ o′}
  → {f : Net i′ o′}
  → substₙ (sym i≡) (sym o≡) f ⨾ idₛ o≡ ≡ idₛ i≡ ⨾ f
⨾-idₛ {i≡ = i≡} {o≡ = o≡} rewrite i≡ | o≡ = refl

F-Monoidal : Monoidal F
F-Monoidal = monoidalHelper F (record
  { ⊗ = Tensor
  ; unit = 0
  ; unitorˡ = record { from = id ; to = id ; iso = record { isoˡ = refl ; isoʳ = refl } }
  ; unitorʳ = record
    { from = idₛ +0
    ; to = idₛ (sym +0)
    ; iso = record
      { isoˡ = funext λ x → subst-sym-subst {P = Fin} +0
      ; isoʳ = funext λ x → subst-subst-sym {P = Fin} +0 } }
  ; associator = λ{ {x} {y} {z} → record
    { from = idₛ (+-assoc x y z)
    ; to = idₛ (sym (+-assoc x y z))
    ; iso = record
      { isoˡ = funext λ _ → subst-sym-subst {P = Fin} (+-assoc x y z)
      ; isoʳ = funext λ _ → subst-subst-sym {P = Fin} (+-assoc x y z) } } }
  ; unitorˡ-commute = refl
  ; unitorʳ-commute = unitorʳ-commute
  ; assoc-commute = λ{ {i} → assoc-commute {i}}
  ; triangle = {!   !}
  ; pentagon = {!   !}
  })
  where
  open Bifunctor
  Tensor : Bifunctor F F F
  Tensor .F₀ = uncurry _+_
  Tensor .F₁ = uncurry _⊗_
  Tensor .identity {i , i′} = id⊗id {i} {i′}
  Tensor .homomorphism {_} {_} {_} {f , _} {g , _} = ⊗-⨾-distr {f₁ = f} {g₁ = g}
  Tensor .F-resp-≈ (f≡g₁ , f≡g₂) rewrite f≡g₁ | f≡g₂ = refl

  unitorʳ-commute : {i o : ℕ} {f : Net i o} → f ⊗ id₀ ⨾ idₛ +0 ≡ idₛ +0 ⨾ f
  unitorʳ-commute {i} {o} {f} = begin
      f ⊗ id₀ ⨾ idₛ +0
    ≡⟨ cong (_⨾ idₛ +0) ⊗-empty ⟩
      substₙ +0′ +0′ f ⨾ idₛ +0
    ≡⟨ ⨾-idₛ {f = f} ⟩
      idₛ +0 ⨾ f
    ∎

  assoc-commute : {i o : ℕ} {f : Net i o} {i′ o′ : ℕ} {g : Net i′ o′} {i″ o″ : ℕ} {h : Net i″ o″}
    → (f ⊗ g ⊗ h) ⨾ (idₛ (+-assoc o o′ o″)) ≡ idₛ (+-assoc i i′ i″) ⨾ f ⊗ (g ⊗ h)
  assoc-commute {i} {o} {f} {i′} {o′} {g} {i″} {o″} {h} =
    begin
      f ⊗ g ⊗ h ⨾ idₛ assocᵒ
    ≡⟨ cong (_⨾ idₛ assocᵒ) (⊗-assoc {f = f}) ⟩
      substₙ (sym assocⁱ) (sym assocᵒ) (f ⊗ (g ⊗ h)) ⨾ idₛ assocᵒ
    ≡⟨ ⨾-idₛ {f = f ⊗ (g ⊗ h)} ⟩
      idₛ assocⁱ ⨾ f ⊗ (g ⊗ h)
    ∎
    where
      assocⁱ = +-assoc i i′ i″
      assocᵒ = +-assoc o o′ o″
