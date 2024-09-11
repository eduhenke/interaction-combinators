open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)
open Eq.≡-Reasoning

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
  id₀ : Net 0 0
  id₁ : Net 1 1
  τ : Net 2 2
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

  -- ⨾-id : ∀ {i : ℕ} {a : Net i 1} → (a ⨾ id₁) ≡ a

infixl 3 _⨾_
infixl 4 _⊕_

mirror : ∀ {i o} → Net i o → Net o i
mirror (a ⊕ b) = mirror a ⊕ mirror b
mirror (a ⨾ b) = mirror b ⨾ mirror a
mirror ε⁺ = ε⁻
mirror ε⁻ = ε⁺
mirror δ⁺ = δ⁻
mirror δ⁻ = δ⁺
mirror ζ⁺ = ζ⁻
mirror ζ⁻ = ζ⁺
mirror id₀ = id₀
mirror id₁ = id₁
mirror τ = τ

id : ∀ {i} → Net i i
id {0} = id₀
id {suc i} = id₁ ⊕ id {i} 

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
-- reduce (ε⁺ ⨾ id₁) = ε⁺
-- reduce (ε⁺ ⨾ id₀ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ id₁ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ c ⊕ c₂ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ (c ⨾ c₂) ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ ε⁺ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ ε⁻ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ δ⁻ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ ζ⁻ ⊕ c₁) = {!   !}
-- reduce (ε⁺ ⨾ (c ⨾ c₁)) = ⨁⁺ ε⁺ ⨾ c₁
-- reduce (ε⁺ ⨾ ε⁻) = id₀
-- reduce (ε⁺ ⨾ δ⁻) = ε⁺ ⊕ ε⁺
-- reduce (ε⁺ ⨾ ζ⁻) = ε⁺ ⊕ ε⁺
-- reduce (_  ⨾ ε⁻) = ⨁⁻ ε⁻
-- reduce (x₁ ⊕ x₂ ⨾ τ ⨾ y₁ ⊕ y₂) = {!   !}
-- reduce (δ⁺ ⨾ δ⁻) = τ
-- reduce (ζ⁺ ⨾ ζ⁻) = τ
-- reduce (ζ⁺ ⨾ δ⁻) = δ⁻ ⊕ δ⁻ ⨾ id₁ ⊕ τ ⊕ id₁ ⨾ ζ⁺ ⊕ ζ⁺
-- reduce (δ⁺ ⨾ ζ⁻) = ζ⁻ ⊕ ζ⁻ ⨾ id₁ ⊕ τ ⊕ id₁ ⨾ δ⁺ ⊕ δ⁺
-- reduce (a ⊕ b) = reduce a ⊕ reduce b
-- reduce (a ⨾ b) = reduce a ⨾ reduce b
-- reduce scalar = scalar

-- invert₂ : ∀ {o} → Net 2 o → Net 2 o
-- invert₂ τ = id
-- invert₂ (n ⊕ n₁) = {!   !}
-- invert₂ (n ⨾ n₁) = {!   !}
-- invert₂ δ⁺ = {!   !}
-- invert₂ ζ⁺ = {!   !} 


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
  ⊕-empty : ∀ {i o : ℕ} {a : Net i o} → (_⊕_ {{Eq.sym (+-identityʳ i)}} {{Eq.sym (+-identityʳ o)}} a id₀ ≅ a)
  empty-⊕ : ∀ {i o : ℕ} {a : Net i o} → (_⊕_ {{Eq.sym (+-identityˡ i)}} {{Eq.sym (+-identityˡ o)}} id₀ a ≅ a)

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

-- normalize : ∀ {i o : ℕ} → Net i o → Net i o
-- -- ⊕-empty
-- normalize (_⊕_ {i₁} {i₂} {o₁} {o₂} {i} {o} {{i≡}} {{o≡}} a id₀) =
--   Eq.subst
--     (λ x → x)
--     (
--       begin
--         Net i₁ o₁
--       ≡⟨ Eq.cong (λ x → Net x _) (Eq.sym (+-identityʳ _)) ⟩
--         Net (i₁ + 0) o₁
--       ≡⟨ Eq.cong (λ x → Net _ x) (Eq.sym (+-identityʳ _)) ⟩
--         Net (i₁ + 0) (o₁ + 0)
--       ≡⟨ Eq.cong (λ x → Net x _) (Eq.sym i≡) ⟩
--         Net i (o₁ + 0)
--       ≡⟨ Eq.cong (λ x → Net _ x) (Eq.sym o≡) ⟩
--         Net i o
--       ∎
--     )
--     a
-- -- empty-⊕
-- normalize (_⊕_ {i₁} {i₂} {o₁} {o₂} {i} {o} {{i≡}} {{o≡}} id₀ a) =
--   Eq.subst
--     (λ x → x)
--     (
--       begin
--         Net i₂ o₂
--       ≡⟨ Eq.cong (λ x → Net x _) (Eq.sym i≡) ⟩
--         Net i o₂
--       ≡⟨ Eq.cong (λ x → Net _ x) (Eq.sym o≡) ⟩
--         Net i o
--       ∎
--     )
--     a
-- -- ⨾-assoc
-- normalize (a ⨾ (b ⨾ c)) = (a ⨾ b) ⨾ c
-- -- ⊕-assoc
-- normalize (_⊕_ {i₁} {i₂} {o₁} {o₂} {i} {o} {{i'≡}} a (_⊕_ {{i''≡}} b c)) = _⊕_ {{{!   !}}} {{{!   !}}} (a ⊕ b) c
--   where
--     i≡ = Eq.subst (λ x → _ ≡ _ + x) i''≡ i'≡
--     i≡' = Eq.trans i≡ {!   !} --(Eq.sym (+-assoc i₁ i₂ _))
-- -- id-⨾
-- normalize (a ⨾ id₀) = a
-- -- ⨾-id
-- normalize (a ⨾ id₁) = a
-- -- τ-τ
-- normalize (τ ⨾ τ) = id
-- -- ⨾-τ
-- normalize {2} {2} ((_⊕_ {1} {1} {1} {1} id₁ a) ⨾ τ) = τ ⨾ (_⊕_ {{Eq.refl}} {{Eq.refl}} a id₁)
-- normalize (a ⊕ b) = normalize a ⊕ normalize b
-- normalize (a ⨾ b) = normalize a ⨾ normalize b
-- normalize scalar = scalar

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
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ (ζ⁻ ⊕ ζ⁻) ⨾ (id₁ ⊕ τ ⊕ id₁) ⨾ (δ⁺ ⊕ δ⁺)
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ (δ⁻ ⊕ δ⁻) ⨾ (id₁ ⊕ τ ⊕ id₁) ⨾ (ζ⁺ ⊕ ζ⁺)
  
  eq : ∀ {i o : ℕ} {a b c : Net i o}
    → a ≅ b
    → b ⟶ c
    → a ⟶ c

ε-ε→nothing : (ε⁺ ⨾ ε⁻) ⟶ id₀
ε-ε→nothing = ε⁺

ε-id-ε→nothing : ((ε⁺ ⨾ id) ⨾ ε⁻) ⟶ id₀
ε-id-ε→nothing = ε⁻

ε-id-ε-id→nothing : (((ε⁺ ⨾ id) ⨾ ε⁻) ⨾ id) ⟶ id₀
ε-id-ε-id→nothing = eq ⨾-id ε-id-ε→nothing

δ-δ→τ : (δ⁺ ⨾ δ⁻) ⟶ τ
δ-δ→τ = δ-δ

δ-id-δ→τ : (δ⁺ ⨾ id ⨾ δ⁻) ⟶ τ
δ-id-δ→τ = eq
  (trans ⨾-assoc (cong (δ⁺ ⨾_) id-⨾))
  δ-δ
