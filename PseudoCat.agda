open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Data.Fin.Base using (Fin)
open import Data.List
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_) renaming (id to permutationId)
open import Data.Fin.Patterns

import Relation.Nullary using (¬_)
import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax)

open import Relation.Binary
open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to Star-refl)
open import Relation.Binary.Construct.Closure.Symmetric
-- open import Relation.Binary.Construct.Closure.Equivalence
-- import Relation.Binary.Reasoning.Base.Single as Rel-Reasoning
-- import Relation.Binary.Reasoning.Setoid as Setoid-Reasoning

data Net : ℕ → ℕ → Set

variable
  i o : ℕ
  i₁ i₂ i₃ o₁ o₂ o₃ : ℕ
  k k₁ k₂ p q : ℕ
  n n₁ n₂ n₃ : Net i o

infixl 8 _⨾_
infixl 9 _⊗_
data Net where
  -- underlying category theory constructs
  id : Net i i
  τ : Net 2 2
  _⊗_ : {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
    → Net i₁ o₁
    → Net i₂ o₂
    ------------
    → Net i o
  _⨾_ :
      Net i k
    → Net   k o
    → Net i   o
  -- generating operations
  ε⁺ : Net 0 1
  ε⁻ : Net 1 0
  δ⁺ : Net 2 1
  δ⁻ : Net 1 2
  ζ⁺ : Net 2 1
  ζ⁻ : Net 1 2

id₀ = id {0}
id₁ = id {1}

⨁⁺ : Net 0 1 → Net 0 k
⨁⁺ {0} net = id₀
⨁⁺ {suc k} net = net ⊗ (⨁⁺ {k} net)

⨁⁻ : Net 1 0 → Net k 0
⨁⁻ {0} net = id₀
⨁⁻ {suc k} net = net ⊗ (⨁⁻ {k} net)

infixl 1 _∼_ 
-- Small-step syntactical equivalence on nets
data _∼_ : Rel (Net i o) 0ℓ where
  symm : n₁ ∼ n₂ → n₂ ∼ n₁
  ⨾-id : n ⨾ id ∼ n
  id-⨾ : id ⨾ n ∼ n
  ⨾-assoc : ∀ {i o p q : ℕ} → {n₁ : Net i p} → {n₂ : Net p q} → {n₃ : Net q o}
    → n₁ ⨾ n₂ ⨾ n₃ ∼ n₁ ⨾ (n₂ ⨾ n₃)
  ⊗-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {n₁ : Net i₁ o₁}
    → {n₂ : Net i₂ o₂}
    → {n₃ : Net i₃ o₃}
    → (
      (_⊗_ {{i≡}} {{o≡}}
        (n₁ ⊗ n₂) n₃)
      ∼
      (_⊗_ {{Eq.trans i≡ (+-assoc i₁ i₂ i₃)}} {{Eq.trans o≡ (+-assoc o₁ o₂ o₃)}}
        n₁ (n₂ ⊗ n₃)))
  ⊗-empty : (_⊗_ {{Eq.sym (+-identityʳ i)}} {{Eq.sym (+-identityʳ o)}} n (id {0}) ∼ n)
  empty-⊗ : (_⊗_ {{Eq.sym (+-identityˡ i)}} {{Eq.sym (+-identityˡ o)}} (id {0}) n ∼ n)

  distr :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{k≡ : k ≡ k₁ + k₂}}
    → {a₁ : Net i₁ k₁}
    → {a₂ : Net i₂ k₂}
    → {b₁ : Net k₁ o₁}
    → {b₂ : Net k₂ o₂}
    → (_⊗_ {{i≡}} {{k≡}} a₁ a₂) ⨾ (_⊗_ {{k≡}} {{o≡}} b₁ b₂) ∼ (a₁ ⨾ b₁) ⊗ (a₂ ⨾ b₂)

  τ-τ : τ ⨾ τ ∼ id
  ⨾-τ : ∀ {n : Net 1 1} → (id₁ ⊗ n) ⨾ τ ∼ τ ⨾ (n ⊗ id₁)

  -- structural transitivity
  ⊗₁ : n₁ ∼ n₂ → n₁ ⊗ n ∼ n₂ ⊗ n
  ⊗₂ : n₁ ∼ n₂ → n ⊗ n₁ ∼ n ⊗ n₂
  ⨾₁ : n₁ ∼ n₂ → n₁ ⨾ n ∼ n₂ ⨾ n
  ⨾₂ : n₁ ∼ n₂ → n ⨾ n₁ ∼ n ⨾ n₂

-- Big-step syntactical equivalence
_∼*_ : Rel (Net i o) 0ℓ
_∼*_ = Star _∼_

infix 5 _⟶_
-- Small-step reduction relation
data _⟶_ : Rel (Net i o) 0ℓ where
  ε-δ : ε⁺ ⨾ δ⁻ ⟶ ε⁺ ⊗ ε⁺
  ε-ζ : ε⁺ ⨾ ζ⁻ ⟶ ε⁺ ⊗ ε⁺
  ε-ε : ε⁺ ⨾ ε⁻ ⟶ id₀
  δ-ε : δ⁺ ⨾ ε⁻ ⟶ ε⁻ ⊗ ε⁻
  ζ-ε : ζ⁺ ⨾ ε⁻ ⟶ ε⁻ ⊗ ε⁻
  δ-δ : δ⁺ ⨾ δ⁻ ⟶ τ
  ζ-ζ : ζ⁺ ⨾ ζ⁻ ⟶ τ
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺
  -- structural transitivity
  ⊗₁ : n₁ ⟶ n₂ → n₁ ⊗ n ⟶ n₂ ⊗ n
  ⊗₂ : n₁ ⟶ n₂ → n ⊗ n₁ ⟶ n ⊗ n₂
  ⨾₁ : n₁ ⟶ n₂ → n₁ ⨾ n ⟶ n₂ ⨾ n
  ⨾₂ : n₁ ⟶ n₂ → n ⨾ n₁ ⟶ n ⨾ n₂

-- Small-step equivalence
data _≃'_ : Rel (Net i o) 0ℓ where
  computation : n₁ ⟶ n₂ → n₁ ≃' n₂
  syntactic : n₁ ∼ n₂ → n₁ ≃' n₂

infix  2 _≃_
-- Big-step equivalence
_≃_ : Rel (Net i o) 0ℓ
_≃_ = Star _≃'_

module ≃-Reasoning {i o : ℕ} where
  open import Relation.Binary.Reasoning.Syntax
  open import Relation.Binary.Construct.Closure.ReflexiveTransitive.Properties
  ------------------------------------------------------------------------
  -- Definition of "related to"

  -- This seemingly unnecessary type is used to make it possible to
  -- infer arguments even if the underlying equality evaluates.

  infix 4 _IsRelatedTo_

  data _IsRelatedTo_ (x y : Net i o) : Set where
    relTo : (x≃y : x ≃ y) → x IsRelatedTo y

  start : _IsRelatedTo_ ⇒ _≃_
  start (relTo x≃y) = x≃y

  ⟶-go : Trans _⟶_ _IsRelatedTo_ _IsRelatedTo_
  ⟶-go x⟶y (relTo y≃z) = relTo (computation x⟶y ◅ y≃z)
  
  ∼-go : Trans _∼_ _IsRelatedTo_ _IsRelatedTo_
  ∼-go x∼y (relTo y≃z) = relTo (syntactic x∼y ◅ y≃z)

  stop : Reflexive _IsRelatedTo_
  stop = relTo (reflexive _≃'_ Eq.refl)

  ------------------------------------------------------------------------
  -- Reasoning combinators

  open begin-syntax _IsRelatedTo_ start public
  open end-syntax _IsRelatedTo_ stop public
  open ⟶-syntax _IsRelatedTo_ _IsRelatedTo_ ⟶-go public
  open ∼-syntax _IsRelatedTo_ _IsRelatedTo_ ∼-go public

open ≃-Reasoning

ε-ε→empty : ε⁺ ⨾ ε⁻ ≃ id₀
ε-ε→empty = begin
  ε⁺ ⨾ ε⁻ ⟶⟨ ε-ε ⟩
  id₀     ∎

ε-id-ε→empty : ε⁺ ⨾ id ⨾ ε⁻ ≃ id₀
ε-id-ε→empty = begin
  ε⁺ ⨾ id ⨾ ε⁻  ∼⟨ ⨾₁ ⨾-id ⟩
  ε⁺ ⨾ ε⁻       ⟶⟨ ε-ε ⟩
  id₀           ∎

ε-id-ε-id→empty : ε⁺ ⨾ id ⨾ ε⁻ ⨾ id ≃ id₀
ε-id-ε-id→empty = begin
  ε⁺ ⨾ id ⨾ ε⁻ ⨾ id  ∼⟨ ⨾-id ⟩
  ε⁺ ⨾ id ⨾ ε⁻       ∼⟨ ⨾₁ ⨾-id ⟩
  ε⁺ ⨾ ε⁻            ⟶⟨ ε-ε ⟩
  id₀                ∎

δ-id-δ→τ : (δ⁺ ⨾ id ⨾ δ⁻) ≃ τ
δ-id-δ→τ = begin
  δ⁺ ⨾ id ⨾ δ⁻  ∼⟨ ⨾₁ ⨾-id ⟩
  δ⁺ ⨾ δ⁻       ⟶⟨ δ-δ ⟩
  τ             ∎

δ²⨾δ² : δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻ ≃ τ ⊗ τ
δ²⨾δ² = begin
  δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻     ∼⟨ distr ⟩
  (δ⁺ ⨾ δ⁻) ⊗ (δ⁺ ⨾ δ⁻) ⟶⟨ ⊗₁ δ-δ ⟩
  τ ⊗ (δ⁺ ⨾ δ⁻)         ⟶⟨ ⊗₂ δ-δ ⟩
  τ ⊗ τ                 ∎

-- ≃-confluent :
--     n ≃ n₁
--   → n ≃ n₂
--   → n₁ ≃ n₂
-- ≃-confluent Star-refl Star-refl = Star-refl
-- ≃-confluent Star-refl x = x
-- ≃-confluent (x ◅ x₁) Star-refl = {!   !}
-- ≃-confluent (x ◅ x₁) (x₂ ◅ y) = {!   !}