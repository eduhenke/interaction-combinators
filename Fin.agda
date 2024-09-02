import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Fin.Base using (Fin; join; splitAt)
open import Function.Base using (_∘_; flip)
open import Data.Sum using (_⊎_; inj₁; inj₂; [_,_]′)
import Data.Sum as Sum
import Data.Fin.Permutation as Permutation
open import Function.Base using (id)
open import Data.Fin.Patterns
open import Function.Bundles using (_↔_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Empty
open import Data.Unit
open import Data.Product

Net : ℕ → ℕ → Set
Net i o = Fin (suc i) → Fin (suc o)

infixl 6 _⨾_
_⨾_ : ∀ {i o k : ℕ}
  → Net i k
  → Net   k o
  → Net i   o
a ⨾ b = b ∘ a

-- infixl 6 _⊕_
-- _⊕_ : ∀ {i₁ i₂ o₁ o₂ i o : ℕ} → {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
--   → Net i₁ o₁
--   → Net i₂ o₂
--   ------------
--   → Net i o
-- _⊕_ {i₁} {i₂} {o₁} {o₂} {{i≡+}} {{o≡+}} a b x =
--   let i₁⊎i₂ = splitAt i₁ (Eq.subst Fin i≡+ x)
--       o₁⊎o₂ = Sum.map a b i₁⊎i₂
--       o' = join _ _ o₁⊎o₂
--       o = Eq.subst Fin (Eq.sym o≡+) o'
--   in o

id₁ : Net 1 1
id₁ = id

empty : Net 0 0
empty = id

τ : Net 2 2
τ c = {!   !}

ε⁺ : Net 0 1
ε⁺ = {!   !}

ε⁻ : Net 1 0
ε⁻ 0F = {!   !}
ε⁻ (Fin.suc c) = {!   !}

-- -- δ⁺ : Net 2 1
-- -- δ⁺ = {!   !}
-- -- δ⁻ : Net 1 2
-- -- δ⁻ = {!   !}
-- -- ζ⁺ : Net 2 1
-- -- ζ⁺ = {!   !}
-- -- ζ⁻ : Net 1 2
-- -- ζ⁻ = {!   !}

-- ⨾-id : ∀ {i o : ℕ} {n : Net i o}
--       → n ⨾ id ≡ n
-- ⨾-id = refl

-- id-⨾ : ∀ {i o : ℕ} {n : Net i o}
--        → id ⨾ n ≡ n
-- id-⨾ = refl

-- ⨾-assoc : ∀ {i o p q : ℕ}
--             {a : Net i p} {b : Net p q} {c : Net q o}
--             → (a ⨾ b) ⨾ c ≡ a ⨾ (b ⨾ c)
-- ⨾-assoc = refl

-- ⊕-assoc : ∀ {i o i₁ i₂ i₃ o₁ o₂ o₃ : ℕ}
--   → {{x : i ≡ i₁ + i₂ + i₃}}
--   → {{y : o ≡ o₁ + o₂ + o₃}}
--   → (a : Net i₁ o₁)
--   → (b : Net i₂ o₂)
--   → (c : Net i₃ o₃)
--   → (
--     (_⊕_ {{x}} {{y}}
--       (a ⊕ b) c)
--     ≡
--     (_⊕_ {{Eq.trans x (+-assoc i₁ i₂ i₃)}} {{Eq.trans y (+-assoc o₁ o₂ o₃)}}
--       a (b ⊕ c)))
-- ⊕-assoc a b c =
--   begin
--     ((a ⊕ b) ⊕ c)
--   ≡⟨⟩
--     {!   !}
--   ≡⟨⟩
--     {!   !}
--   ≡⟨⟩ 
--     {!   !} 