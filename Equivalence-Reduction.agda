open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Data.Fin.Base using (Fin)
open import Data.List
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_) renaming (id to permutationId)
open import Data.Fin.Patterns
open import Function.Base hiding (id)

open import Relation.Nullary using (¬_)
open import Data.Product using (Σ; _,_; ∃; Σ-syntax; ∃-syntax; _×_; proj₁; proj₂)

open import Relation.Binary
open import Level
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
open import Relation.Binary.Construct.Closure.Symmetric
open import Relation.Binary.Construct.Closure.Equivalence hiding (reflexive; transitive)
open import Relation.Binary.Rewriting

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

infixl 1 _~′_ 
-- Small-step syntactical equivalence on nets
data _~′_ : Rel (Net i o) 0ℓ where
  symm : n₁ ~′ n₂ → n₂ ~′ n₁
  ⨾-id : n ⨾ id ~′ n
  id-⨾ : id ⨾ n ~′ n
  ⨾-assoc : ∀ {i o p q : ℕ} → {n₁ : Net i p} → {n₂ : Net p q} → {n₃ : Net q o}
    → n₁ ⨾ n₂ ⨾ n₃ ~′ n₁ ⨾ (n₂ ⨾ n₃)
  ⊗-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {n₁ : Net i₁ o₁}
    → {n₂ : Net i₂ o₂}
    → {n₃ : Net i₃ o₃}
    → (
      (_⊗_ {{i≡}} {{o≡}}
        (n₁ ⊗ n₂) n₃)
      ~′
      (_⊗_ {{Eq.trans i≡ (+-assoc i₁ i₂ i₃)}} {{Eq.trans o≡ (+-assoc o₁ o₂ o₃)}}
        n₁ (n₂ ⊗ n₃)))
  ⊗-empty : (_⊗_ {{Eq.sym (+-identityʳ i)}} {{Eq.sym (+-identityʳ o)}} n (id {0}) ~′ n)
  empty-⊗ : (_⊗_ {{Eq.sym (+-identityˡ i)}} {{Eq.sym (+-identityˡ o)}} (id {0}) n ~′ n)

  distr :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{k≡ : k ≡ k₁ + k₂}}
    → {a₁ : Net i₁ k₁}
    → {a₂ : Net i₂ k₂}
    → {b₁ : Net k₁ o₁}
    → {b₂ : Net k₂ o₂}
    → (_⊗_ {{i≡}} {{k≡}} a₁ a₂) ⨾ (_⊗_ {{k≡}} {{o≡}} b₁ b₂) ~′ (a₁ ⨾ b₁) ⊗ (a₂ ⨾ b₂)

  τ-τ : τ ⨾ τ ~′ id
  ⨾-τ : ∀ {n : Net 1 1} → (id₁ ⊗ n) ⨾ τ ~′ τ ⨾ (n ⊗ id₁)

  -- structural transitivity
  ⊗₁ : n₁ ~′ n₂ → n₁ ⊗ n ~′ n₂ ⊗ n
  ⊗₂ : n₁ ~′ n₂ → n ⊗ n₁ ~′ n ⊗ n₂
  ⨾₁ : n₁ ~′ n₂ → n₁ ⨾ n ~′ n₂ ⨾ n
  ⨾₂ : n₁ ~′ n₂ → n ⨾ n₁ ~′ n ⨾ n₂

-- Syntactical equivalence
_~_ : Rel (Net i o) 0ℓ
_~_ = EqClosure _~′_

infix 5 _⟶ʳ_
-- Small-step reduction relation
data _⟶ʳ_ : Rel (Net i o) 0ℓ where
  ε-δ : ε⁺ ⨾ δ⁻ ⟶ʳ ε⁺ ⊗ ε⁺
  ε-ζ : ε⁺ ⨾ ζ⁻ ⟶ʳ ε⁺ ⊗ ε⁺
  ε-ε : ε⁺ ⨾ ε⁻ ⟶ʳ id₀
  δ-ε : δ⁺ ⨾ ε⁻ ⟶ʳ ε⁻ ⊗ ε⁻
  ζ-ε : ζ⁺ ⨾ ε⁻ ⟶ʳ ε⁻ ⊗ ε⁻
  δ-δ : δ⁺ ⨾ δ⁻ ⟶ʳ τ
  ζ-ζ : ζ⁺ ⨾ ζ⁻ ⟶ʳ τ
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ʳ ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ʳ δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺
  -- structural transitivity
  ⊗₁ : n₁ ⟶ʳ n₂ → n₁ ⊗ n ⟶ʳ n₂ ⊗ n
  ⊗₂ : n₁ ⟶ʳ n₂ → n ⊗ n₁ ⟶ʳ n ⊗ n₂
  ⨾₁ : n₁ ⟶ʳ n₂ → n₁ ⨾ n ⟶ʳ n₂ ⨾ n
  ⨾₂ : n₁ ⟶ʳ n₂ → n ⨾ n₁ ⟶ʳ n ⨾ n₂


infix  2 _⟶_
_⟶_ : Rel (Net i o) 0ℓ
n₁ ⟶ n₂ = ∃ λ k → n₁ ~ k × k ⟶ʳ n₂


infix  2 _⟶*_
_⟶*_ : Rel (Net i o) 0ℓ
_⟶*_ = Star _⟶_

module ⟶-Reasoning where
  infixr 2 step-⟶ʳ
  step-⟶ʳ : ∀ (x : Net i o) {y z}
    → y ⟶* z
    → x ⟶ʳ y
    ----------
    → x ⟶* z
  step-⟶ʳ x y⟶*z x⟶ʳy = (_ , ⊘ , x⟶ʳy) ◅ y⟶*z
  syntax step-⟶ʳ x y⟶*z x⟶ʳy = x ⟶ʳ⟨ x⟶ʳy ⟩ y⟶*z

  infixr 2 step-~-⟶
  step-~-⟶ : ∀ (x k : Net i o) {y z}
    → y ⟶* z
    → x ~ k
    → k ⟶ʳ y
    ----------
    → x ⟶* z
  step-~-⟶ x _ y⟶*z x~k k⟶ʳy = (_ , x~k , k⟶ʳy) ◅ y⟶*z
  syntax step-~-⟶ x k y⟶*z x~k k⟶ʳy = x ~⟨ x~k ⟩ k ⟶⟨ k⟶ʳy ⟩ y⟶*z

  _∎ : (n : Net i o) → n ⟶* n
  n ∎ = ⊘

open ⟶-Reasoning

module ⟶-examples where
  ε-ε→empty : ε⁺ ⨾ ε⁻ ⟶* id₀
  ε-ε→empty =
    ε⁺ ⨾ ε⁻   ⟶ʳ⟨ ε-ε ⟩
    id₀       ∎

  ε-id-ε→empty : ε⁺ ⨾ id ⨾ ε⁻ ⟶* id₀
  ε-id-ε→empty = 
    ε⁺ ⨾ id ⨾ ε⁻ ~⟨ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    ε⁺ ⨾ ε⁻     ⟶⟨ ε-ε ⟩
    id₀         ∎

  ε-id-ε-id→empty : ε⁺ ⨾ id ⨾ ε⁻ ⨾ id ⟶* id₀
  ε-id-ε-id→empty =
    ε⁺ ⨾ id ⨾ ε⁻ ⨾ id    ~⟨ fwd ⨾-id ◅ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    ε⁺ ⨾ ε⁻             ⟶⟨ ε-ε ⟩
    id₀                 ∎

  δ-id-δ→τ : (δ⁺ ⨾ id ⨾ δ⁻) ⟶* τ
  δ-id-δ→τ =
    δ⁺ ⨾ id ⨾ δ⁻ ~⟨ fwd (⨾₁ ⨾-id) ◅ ⊘ ⟩
    δ⁺ ⨾ δ⁻      ⟶⟨ δ-δ ⟩
    τ            ∎

  δ²⨾δ² : δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻ ⟶* τ ⊗ τ
  δ²⨾δ² =
    δ⁺ ⊗ δ⁺ ⨾ δ⁻ ⊗ δ⁻     ~⟨ fwd distr ◅ ⊘ ⟩
    (δ⁺ ⨾ δ⁻) ⊗ (δ⁺ ⨾ δ⁻)  ⟶⟨ ⊗₁ δ-δ ⟩
    τ ⊗ (δ⁺ ⨾ δ⁻)          ⟶ʳ⟨ ⊗₂ δ-δ ⟩
    (τ ⊗ τ)                   ∎

_⟶ʳ*_ : Rel (Net i o) 0ℓ
_⟶ʳ*_ = Star _⟶ʳ_

⊗₁* : ∀ {i o i′ o′ : ℕ} {a b : Net i o} {k : Net i′ o′}
  → a ⟶ʳ* b
  → (a ⊗ k) ⟶ʳ* (b ⊗ k)
⊗₁* ⊘ = ⊘
⊗₁* (a⟶j ◅ j⟶*b) = ⊗₁ a⟶j ◅ ⊗₁* j⟶*b

⊗₂* : ∀ {i o i′ o′ : ℕ} {a b : Net i o} {k : Net i′ o′}
  → a ⟶ʳ* b
  → (k ⊗ a) ⟶ʳ* (k ⊗ b)
⊗₂* ⊘ = ⊘
⊗₂* (a⟶j ◅ j⟶*b) = ⊗₂ a⟶j ◅ ⊗₂* j⟶*b

⨾₁* : ∀ {i m o : ℕ} {a b : Net i m} {k : Net m o}
  → a ⟶ʳ* b
  → (a ⨾ k) ⟶ʳ* (b ⨾ k)
⨾₁* ⊘ = ⊘
⨾₁* (a⟶j ◅ j⟶*b) = ⨾₁ a⟶j ◅ ⨾₁* j⟶*b

⨾₂* : ∀ {i m o : ℕ} {a b : Net m o} {k : Net i m}
  → a ⟶ʳ* b
  → (k ⨾ a) ⟶ʳ* (k ⨾ b)
⨾₂* ⊘ = ⊘
⨾₂* (a⟶j ◅ j⟶*b) = ⨾₂ a⟶j ◅ ⨾₂* j⟶*b

{-# TERMINATING #-} -- TODO: remove
⟶ʳ-confluent : ∀ {i o : ℕ} → Confluent (_⟶ʳ_ {i} {o})
-- trivial empty cases
⟶ʳ-confluent {A = a} ⊘ ⊘ = a , ⊘ , ⊘
⟶ʳ-confluent {C = c} ⊘ a⟶*c = c , (a⟶*c , ⊘)
⟶ʳ-confluent {B = b} a⟶*b ⊘ = b , (⊘ , a⟶*b)
-- atomic cases
⟶ʳ-confluent (ε-δ ◅ a⟶*b) (ε-δ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (ε-ζ ◅ a⟶*b) (ε-ζ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (ε-ε ◅ a⟶*b) (ε-ε ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (δ-ε ◅ a⟶*b) (δ-ε ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (ζ-ε ◅ a⟶*b) (ζ-ε ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (δ-δ ◅ a⟶*b) (δ-δ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (ζ-ζ ◅ a⟶*b) (ζ-ζ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (δ-ζ ◅ a⟶*b) (δ-ζ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
⟶ʳ-confluent (ζ-δ ◅ a⟶*b) (ζ-δ ◅ a⟶*c) = ⟶ʳ-confluent a⟶*b a⟶*c
-- structural transitivity cases
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⊗₁ a⟶b) ◅ ⊘) ((⊗₁ a⟶c) ◅ ⊘) =
  let d , b⟶d , c⟶d = ⟶ʳ-confluent (a⟶b ◅ ⊘) (a⟶c ◅ ⊘)
  in (d ⊗ _) , ⊗₁* b⟶d , ⊗₁* c⟶d
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⊗₁ a⟶b) ◅ ⊘) ((⊗₂ a⟶c) ◅ ⊘) =
  _ , ⊗₂ a⟶c ◅ ⊘ , ⊗₁ a⟶b ◅ ⊘
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⊗₂ a⟶b) ◅ ⊘) ((⊗₁ a⟶c) ◅ ⊘) =
  _ , ⊗₁ a⟶c ◅ ⊘ , ⊗₂ a⟶b ◅ ⊘
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⊗₂ a⟶b) ◅ ⊘) ((⊗₂ a⟶c) ◅ ⊘) =
  let d , b⟶d , c⟶d = ⟶ʳ-confluent (a⟶b ◅ ⊘) (a⟶c ◅ ⊘)
  in (_ ⊗ d) , ⊗₂* b⟶d , ⊗₂* c⟶d
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⨾₁ a⟶b) ◅ ⊘) ((⨾₁ a⟶c) ◅ ⊘) =
  let d , b⟶d , c⟶d = ⟶ʳ-confluent (a⟶b ◅ ⊘) (a⟶c ◅ ⊘)
  in (d ⨾ _) , ⨾₁* b⟶d , ⨾₁* c⟶d
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⨾₁ a⟶b) ◅ ⊘) ((⨾₂ a⟶c) ◅ ⊘) =
  _ , ⨾₂ a⟶c ◅ ⊘ , ⨾₁ a⟶b ◅ ⊘
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⨾₂ a⟶b) ◅ ⊘) ((⨾₁ a⟶c) ◅ ⊘) =
  _ , ⨾₁ a⟶c ◅ ⊘ , ⨾₂ a⟶b ◅ ⊘
⟶ʳ-confluent {A = a} {B = b} {C = c} ((⨾₂ a⟶b) ◅ ⊘) ((⨾₂ a⟶c) ◅ ⊘) =
  let d , b⟶d , c⟶d = ⟶ʳ-confluent (a⟶b ◅ ⊘) (a⟶c ◅ ⊘)
  in (_ ⨾ d) , ⨾₂* b⟶d , ⨾₂* c⟶d
-- general inductive step
⟶ʳ-confluent {A = a} {B = b} {C = c} (a⟶b′ ◅ b′⟶*b) (a⟶c′ ◅ c′⟶*c) = {!   !}
  -- let
  --   d , b′⟶*d , c′⟶*d = ⟶ʳ-confluent (a⟶b′ ◅ ⊘) (a⟶c′ ◅ ⊘)
  --   e , d⟶*e , b⟶*e = ⟶ʳ-confluent b′⟶*d b′⟶*b
  --   f , d⟶*f , c⟶*f = ⟶ʳ-confluent c′⟶*d c′⟶*c
  --   g , e⟶*g , f⟶*g = ⟶ʳ-confluent d⟶*e d⟶*f
  --   b⟶*g = b⟶*e ◅◅ e⟶*g
  --   c⟶*g = c⟶*f ◅◅ f⟶*g
  -- in
  --   g , b⟶*g , c⟶*g


-- confluent-example₁ = 
--   let a = ⟶ʳ-confluent (⨾₁ (⊗₁ ε-ε) ◅ ⨾₂ ε-ε ◅ ⊘) (⨾₁ (⊗₂ ε-ε) ◅ ⨾₁ ((⊗₁ ε-ε)) ◅ ⊘)
--   in {!   !}