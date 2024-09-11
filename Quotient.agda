{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
-- open import Cubical.Data.Nat.Properties using (+-assoc)
import Data.Fin.Permutation as Permutation
open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_)
open import Data.Fin.Patterns

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-identityˡ : ∀ (m : ℕ) → 0 + m ≡ m
+-identityˡ m = refl

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

data Net : ℕ → ℕ → Set
variable
  i o : ℕ
  i₁ i₂ i₃ o₁ o₂ o₃ : ℕ
  k k₁ k₂ p q : ℕ
  n : Net i o

Permutation-τ : Permutation 2 2
Permutation-τ = Permutation.transpose 0F 1F

data Net where
  -- underlying category theory constructs
  -- id₀ : Net 0 0
  -- id₁ : Net 1 1
  -- τ : Net 2 2
  wiring : ∀ {i : ℕ} → Permutation i i → Net i i
  _⊕_ : {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
    → Net i₁ o₁
    → Net i₂ o₂
    ------------
    → Net i o
  _⨾_ : Net i k
    →  Net   k o
    →  Net i   o
  -- generating operations
  ε⁺ : Net 0 1
  ε⁻ : Net 1 0
  δ⁺ : Net 2 1
  δ⁻ : Net 1 2
  ζ⁺ : Net 2 1
  ζ⁻ : Net 1 2
  
  ⨾-id : n ⨾ wiring Permutation.id ≡ n
  id-⨟ : wiring Permutation.id ⨾ n ≡ n
  ⨾-assoc : ∀ {a : Net i p} → {b : Net p q} → {c : Net q o}
    → ((a ⨾ b) ⨾ c) ≡ (a ⨾ (b ⨾ c))
  ⊕-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {a : Net i₁ o₁}
    → {b : Net i₂ o₂}
    → {c : Net i₃ o₃}
    → (
      (_⊕_ {{i≡}} {{o≡}}
        (_⊕_ {{refl}} {{refl}} a b) c)
      ≡
      (_⊕_ {{i≡ ∙ (+-assoc i₁ i₂ i₃)}} {{o≡ ∙ (+-assoc o₁ o₂ o₃)}}
        a (_⊕_ {{refl}} {{refl}} b c)))
  ⊕-empty : ∀ {a : Net i o} → ((_⊕_
    {{sym (+-identityʳ i)}}
    {{sym (+-identityʳ o)}}
    a (wiring {0} Permutation.id)) ≡ a)
  empty-⊕ : ∀ {i o : ℕ} {a : Net i o} → ((
    _⊕_
    {{sym (+-identityˡ i)}}
    {{sym (+-identityˡ o)}}
    (wiring {0} Permutation.id) a) ≡ a)

  ⊕-⨾-dist :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{k≡ : k ≡ k₁ + k₂}}
    → {a₁ : Net i₁ k₁}
    → {a₂ : Net i₂ k₂}
    → {b₁ : Net k₁ o₁}
    → {b₂ : Net k₂ o₂}
    → (_⊕_ {{i≡}} {{k≡}} a₁ a₂) ⨾ (_⊕_ {{k≡}} {{o≡}} b₁ b₂) ≡ (a₁ ⨾ b₁) ⊕ (a₂ ⨾ b₂)
  
  τ-τ : wiring Permutation-τ ⨾ wiring Permutation-τ ≡ wiring Permutation.id
  ⨾-τ : ∀ {a : Net 1 1}
    → (_⊕_ {{refl}} {{refl}} (wiring {1} Permutation.id) a) ⨾ (wiring Permutation-τ)
    ≡ (wiring Permutation-τ) ⨾ (_⊕_ {{refl}} {{refl}} a (wiring {1} Permutation.id))
infixl 5 _⨾_
infixl 6 _⊕_

id : Net i i
id = wiring Permutation.id

id₀ : Net 0 0
id₀ = wiring Permutation.id

id₁ : Net 1 1
id₁ = wiring Permutation.id

τ : Net 2 2
τ = wiring Permutation-τ

⨁⁺ : ∀ {k} → Net 0 1 → Net 0 k
⨁⁺ {0} net = id
⨁⁺ {suc k} net = _⊕_ {{refl}} {{refl}} net (⨁⁺ {k} net)

⨁⁻ : ∀ {k} → Net 1 0 → Net k 0
⨁⁻ {0} net = id
⨁⁻ {suc k} net = _⊕_ {{refl}} {{refl}} net (⨁⁻ {k} net)


infix 1 _⟶_
data _⟶_ : ∀ {i o : ℕ} → Net i o → Net i o → Set where
  ε⁺ : ∀ {n : Net 1 o} → (ε⁺ ⨾ n) ⟶ ⨁⁺ ε⁺
  ε⁻ : ∀ {n : Net i 1} → (n ⨾ ε⁻) ⟶ ⨁⁻ ε⁻
  δ-δ : δ⁺ ⨾ δ⁻ ⟶ τ
  ζ-ζ : ζ⁺ ⨾ ζ⁻ ⟶ τ
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ (_⊕_ {{refl}} {{refl}} ζ⁻ ζ⁻) ⨾ (_⊕_ {{refl}} {{refl}} (_⊕_ {{refl}} {{refl}} id₁ τ) id₁) ⨾ (_⊕_ {{refl}} {{refl}} δ⁺ δ⁺)
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ (_⊕_ {{refl}} {{refl}} δ⁻ δ⁻) ⨾ (_⊕_ {{refl}} {{refl}} (_⊕_ {{refl}} {{refl}} id₁ τ) id₁) ⨾ (_⊕_ {{refl}} {{refl}} ζ⁺ ζ⁺)


ε-ε⟶nothing : (ε⁺ ⨾ ε⁻) ⟶ id₀
ε-ε⟶nothing = ε⁺

ε-id-ε⟶nothing : ((ε⁺ ⨾ id) ⨾ ε⁻) ⟶ id₀
ε-id-ε⟶nothing = subst (λ x → x ⨾ ε⁻ ⟶ id₀) (
    ε⁺
  ≡⟨ sym ⨾-id ⟩
    ε⁺ ⨾ id
  ∎) ε-ε⟶nothing

ε⟶≡ : ((ε⁺ ⨾ ε⁻) ⟶ id₀) ≡ (((ε⁺ ⨾ id) ⨾ ε⁻) ⟶ id₀)
ε⟶≡ =
    (ε⁺ ⨾ ε⁻ ⟶ id₀)
  ≡⟨ cong (λ a → a ⨾ ε⁻ ⟶ id₀) (sym ⨾-id) ⟩
    (ε⁺ ⨾ id ⨾ ε⁻ ⟶ id₀)
  ∎

