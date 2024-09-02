open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
import Relation.Binary.Reasoning.Setoid as SEq

open import Data.Fin.Base using (Fin)
open import Data.List
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_) renaming (id to permutationId)
open import Data.Fin.Patterns

-- id, τ
-- Σ = (Σ⁰, Σ¹)
-- Σ⁰ = {()}
-- Σ¹ = {δ⁺, δ⁻, ζ⁺, ζ⁻, ε⁺, ε⁻}
data Net : ℕ → ℕ → Set where
  -- underlying category theory constructs
  wiring : ∀ {i} → (w : Permutation i i) → Net i i
  _⊕_ : ∀ {i₁ i₂ o₁ o₂ i o : ℕ} → {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
    → Net i₁ o₁
    → Net i₂ o₂
    ------------
    → Net i o
  _⨾_ : ∀ {i o k : ℕ}
    → Net i k
    → Net   k o
    → Net i   o
  -- generating operations
  ε⁺ : Net 0 1
  ε⁻ : Net 1 0
  δ⁺ : Net 2 1
  δ⁻ : Net 1 2
  ζ⁺ : Net 2 1
  ζ⁻ : Net 1 2

infixl 2 _⨾_
infixl 2 _⊕_

mirror : ∀ {i o} → Net i o → Net o i
mirror (wiring w) = wiring (flip w)
mirror (a ⊕ b) = mirror a ⊕ mirror b
mirror (a ⨾ b) = mirror b ⨾ mirror a
mirror ε⁺ = ε⁻
mirror ε⁻ = ε⁺
mirror δ⁺ = δ⁻
mirror δ⁻ = δ⁺
mirror ζ⁺ = ζ⁻
mirror ζ⁻ = ζ⁺

id : ∀ {i} → Net i i
id = Net.wiring permutationId

id₁ : Net 1 1
id₁ = id

empty : Net 0 0
empty = id {0}

τ : Net 2 2
τ = Net.wiring (transpose Fin.zero (Fin.suc Fin.zero))

-- elementary diagram
padWith : ∀ {i o} → (p q : ℕ) → Net i o → Net (p + i + q) (p + o + q)
padWith p q n = ((id {p}) ⊕ n) ⊕ (id {q})

⨁⁺ : ∀ {k} → Net 0 1 → Net 0 k
⨁⁺ {0} net = id
⨁⁺ {suc k} net = net ⊕ (⨁⁺ {k} net)

⨁⁻ : ∀ {k} → Net 1 0 → Net k 0
⨁⁻ {0} net = id
⨁⁻ {suc k} net = net ⊕ (⨁⁻ {k} net)

-- αˢ is {δˢ, ζˢ}
-- ε ; ε   =   id₀
-- ε ; α   =   ε ⊕ ε
-- α₁ ; α₂
--   when equal = τ
--   otherwise  = α₂ ⊕ α₂ ; id₁ ⊕ τ ⊕ id₁ ; α₁ ⊕ α₁
-- reduce : ∀ {i o} → Net i o → Net i o
-- reduce (wiring p ⨾ wiring p') = wiring (p ∘ₚ p')
-- reduce (wiring p ⨾ n) = wiring p ⨾ reduce n
-- -- reduce ((n ⨾ wiring p) ⨾ n') = {!   !}
-- reduce (ε⁺ ⨾ _)  = ⨁⁺ ε⁺
-- reduce (_  ⨾ ε⁻) = ⨁⁻ ε⁻
-- reduce (δ⁺ ⨾ δ⁻) = τ
-- reduce (ζ⁺ ⨾ ζ⁻) = τ
-- reduce (ζ⁺ ⨾ δ⁻) = ((δ⁻ ⊕ δ⁻) ⨾ wiring (transpose 1F 2F)) ⨾ (ζ⁺ ⊕ ζ⁺)
-- reduce (δ⁺ ⨾ ζ⁻) = ((ζ⁻ ⊕ ζ⁻) ⨾ wiring (transpose 1F 2F)) ⨾ (δ⁺ ⊕ δ⁺)
-- reduce (a ⊕ b) = (reduce a) ⊕ (reduce b)
-- reduce (a ⨾ b) = (reduce a) ⨾ (reduce b)
-- reduce scalar = scalar


infixl 1 _≅_ 
data _≅_ : {i o : ℕ} → (a b : Net i o) → Set where
  refl : ∀ {i o : ℕ} {a : Net i o} → a ≅ a
  sym : ∀ {i o : ℕ} {a b : Net i o} → a ≅ b → b ≅ a
  trans : ∀ {i o : ℕ} {a b c : Net i o} → a ≅ b → b ≅ c → a ≅ c
  ⨾-id : ∀ {i o : ℕ} {a : Net i o} → a ⨾ id ≅ a
  id-⨾ : ∀ {i o : ℕ} {a : Net i o} → id ⨾ a ≅ a
  ⨾-assoc : ∀ {i o p q : ℕ} → {a : Net i p} → {b : Net p q} → {c : Net q o}
    → ((a ⨾ b) ⨾ c) ≅ (a ⨾ (b ⨾ c))
  ⊕-assoc : ∀ {i o i₁ i₂ i₃ o₁ o₂ o₃ : ℕ}
    → {{x : i ≡ i₁ + i₂ + i₃}}
    → {{y : o ≡ o₁ + o₂ + o₃}}
    → {a : Net i₁ o₁}
    → {b : Net i₂ o₂}
    → {c : Net i₃ o₃}
    → (
      (_⊕_ {{x}} {{y}}
        (a ⊕ b) c)
      ≅
      (_⊕_ {{Eq.trans x (+-assoc i₁ i₂ i₃)}} {{Eq.trans y (+-assoc o₁ o₂ o₃)}}
        a (b ⊕ c)))
  ⊕-empty : ∀ {i o : ℕ} {a : Net i o} → (_⊕_ {{Eq.sym (+-identityʳ i)}} {{Eq.sym (+-identityʳ o)}} a empty ≅ a)
  empty-⊕ : ∀ {i o : ℕ} {a : Net i o} → (_⊕_ {{Eq.sym (+-identityˡ i)}} {{Eq.sym (+-identityˡ o)}} empty a ≅ a)

  dist : ∀ {i o i₁ i₂ o₁ o₂ k₁ k₂ k : ℕ}
    → {{x : i ≡ i₁ + i₂}}
    → {{y : o ≡ o₁ + o₂}}
    → {{z : k ≡ k₁ + k₂}}
    → {a₁ : Net i₁ k₁}
    → {a₂ : Net i₂ k₂}
    → {b₁ : Net k₁ o₁}
    → {b₂ : Net k₂ o₂}
    → (_⊕_ {{x}} {{z}} a₁ a₂) ⨾ (_⊕_ {{z}} {{y}} b₁ b₂) ≅ (a₁ ⨾ b₁) ⊕ (a₂ ⨾ b₂)
  
  τ-τ : τ ⨾ τ ≅ id
  ⨾-τ : ∀ {a : Net 1 1} → (id₁ ⊕ a) ⨾ τ ≅ τ ⨾ (a ⊕ id₁)

cong : ∀ {i o i' o' : ℕ} (f : Net i o → Net i' o') {x y : Net i o}
  → x ≅ y
    ---------
  → f x ≅ f y
cong f n = {!  !}


infix 1 _⟶_
data _⟶_ : ∀ {i o : ℕ} → Net i o → Net i o → Set where
  ε⁺ : ∀ {o : ℕ} {n : Net 1 o} → (ε⁺ ⨾ n) ⟶ ⨁⁺ ε⁺
  ε⁻ : ∀ {i : ℕ} {n : Net i 1} → (n ⨾ ε⁻) ⟶ ⨁⁻ ε⁻
  δ-δ : δ⁺ ⨾ δ⁻ ⟶ τ
  ζ-ζ : ζ⁺ ⨾ ζ⁻ ⟶ τ
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ (ζ⁻ ⊕ ζ⁻) ⨾ wiring (transpose 1F 2F) ⨾ (δ⁺ ⊕ δ⁺)
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ (δ⁻ ⊕ δ⁻) ⨾ wiring (transpose 1F 2F) ⨾ (ζ⁺ ⊕ ζ⁺)
  
  eq : ∀ {i o : ℕ} {a b c : Net i o}
    → a ≅ b
    → b ⟶ c
    → a ⟶ c

ε-ε→nothing : (ε⁺ ⨾ ε⁻) ⟶ empty
ε-ε→nothing = ε⁺

ε-id-ε→nothing : (ε⁺ ⨾ id ⨾ ε⁻) ⟶ empty
ε-id-ε→nothing = ε⁻

δ-δ→nothing : (δ⁺ ⨾ δ⁻) ⟶ τ
δ-δ→nothing = δ-δ

δ-id-δ→nothing : (δ⁺ ⨾ id ⨾ δ⁻) ⟶ τ
δ-id-δ→nothing = eq (trans ⨾-assoc (cong (δ⁺ ⨾_) id-⨾)) δ-δ
