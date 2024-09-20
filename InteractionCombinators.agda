open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_)

open import Data.Fin.Base using (Fin)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Fin.Patterns
open import Function.Base hiding (id)
open import Data.Empty

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
  i o m    : ℕ
  i₁ i₂ i₃ : ℕ
  o₁ o₂ o₃ : ℕ
  m₁ m₂ m₃ : ℕ

  n : Net i o
  a b c k : Net i o

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
      Net i m
    → Net   m o
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

⨁⁺ : Net 0 1 → Net 0 m
⨁⁺ {0} net = id₀
⨁⁺ {suc m} net = net ⊗ (⨁⁺ {m} net)

⨁⁻ : Net 1 0 → Net m 0
⨁⁻ {0} net = id₀
⨁⁻ {suc m} net = net ⊗ (⨁⁻ {m} net)

infixl 1 _~′_ 
-- Small-step syntactical equivalence on nets
data _~′_ : Rel (Net i o) 0ℓ where
  ⨾-id : n ⨾ id ~′ n
  id-⨾ : id ⨾ n ~′ n
  ⨾-assoc : (a ⨾ b) ⨾ c ~′ a ⨾ (b ⨾ c)
  ⊗-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {a : Net i₁ o₁}
    → {b : Net i₂ o₂}
    → {c : Net i₃ o₃}
    → (
      (_⊗_ {{i≡}} {{o≡}}
        (a ⊗ b) c)
      ~′
      (_⊗_ {{Eq.trans i≡ (+-assoc i₁ i₂ i₃)}} {{Eq.trans o≡ (+-assoc o₁ o₂ o₃)}}
        a (b ⊗ c)))
  ⊗-empty : (_⊗_ {{Eq.sym (+-identityʳ i)}} {{Eq.sym (+-identityʳ o)}} n (id {0}) ~′ n)
  empty-⊗ : (_⊗_ {{Eq.sym (+-identityˡ i)}} {{Eq.sym (+-identityˡ o)}} (id {0}) n ~′ n)

  distr :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{m≡ : m ≡ m₁ + m₂}}
    → {a₁ : Net i₁ m₁}
    → {a₂ : Net i₂ m₂}
    → {b₁ : Net m₁ o₁}
    → {b₂ : Net m₂ o₂}
    → (_⊗_ {{i≡}} {{m≡}} a₁ a₂) ⨾ (_⊗_ {{m≡}} {{o≡}} b₁ b₂) ~′ (a₁ ⨾ b₁) ⊗ (a₂ ⨾ b₂)

  τ-τ : τ ⨾ τ ~′ id
  ⨾-τ : ∀ {n : Net 1 1} → (id₁ ⊗ n) ⨾ τ ~′ τ ⨾ (n ⊗ id₁)

  -- structural transitivity
  ⊗₁ : a ~′ b → a ⊗ k ~′ b ⊗ k
  ⊗₂ : a ~′ b → k ⊗ a ~′ k ⊗ b
  ⨾₁ : a ~′ b → a ⨾ k ~′ b ⨾ k
  ⨾₂ : a ~′ b → k ⨾ a ~′ k ⨾ b

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
  ⊗₁ : a ⟶ʳ b → a ⊗ k ⟶ʳ b ⊗ k
  ⊗₂ : a ⟶ʳ b → k ⊗ a ⟶ʳ k ⊗ b
  ⨾₁ : a ⟶ʳ b → a ⨾ k ⟶ʳ b ⨾ k
  ⨾₂ : a ⟶ʳ b → k ⨾ a ⟶ʳ k ⨾ b


infix  2 _⟶_
_⟶_ : Rel (Net i o) 0ℓ
a ⟶ b = ∃ λ k → a ~ k × k ⟶ʳ b


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

infix  2 _⟶ʳ*_
_⟶ʳ*_ : Rel (Net i o) 0ℓ
_⟶ʳ*_ = Star _⟶ʳ_

⊗₁* : a ⟶ʳ* b → a ⊗ k ⟶ʳ* b ⊗ k
⊗₁* ⊘ = ⊘
⊗₁* (a⟶j ◅ j⟶*b) = ⊗₁ a⟶j ◅ ⊗₁* j⟶*b

⊗₂* : a ⟶ʳ* b → k ⊗ a ⟶ʳ* k ⊗ b
⊗₂* ⊘ = ⊘
⊗₂* (a⟶j ◅ j⟶*b) = ⊗₂ a⟶j ◅ ⊗₂* j⟶*b

⨾₁* : a ⟶ʳ* b → a ⨾ k ⟶ʳ* b ⨾ k
⨾₁* ⊘ = ⊘
⨾₁* (a⟶j ◅ j⟶*b) = ⨾₁ a⟶j ◅ ⨾₁* j⟶*b

⨾₂* : a ⟶ʳ* b → k ⨾ a ⟶ʳ* k ⨾ b
⨾₂* ⊘ = ⊘
⨾₂* (a⟶j ◅ j⟶*b) = ⨾₂ a⟶j ◅ ⨾₂* j⟶*b

⟶ʳ-weakly-confluent : WeaklyConfluent (_⟶ʳ_ {i} {o})
-- atomic cases
⟶ʳ-weakly-confluent ε-δ ε-δ = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent ε-ζ ε-ζ = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent ε-ε ε-ε = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent δ-ε δ-ε = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent ζ-ε ζ-ε = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent δ-δ δ-δ = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent ζ-ζ ζ-ζ = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent δ-ζ δ-ζ = _ , ⊘ , ⊘
⟶ʳ-weakly-confluent ζ-δ ζ-δ = _ , ⊘ , ⊘
-- structural transitivity cases
⟶ʳ-weakly-confluent (⊗₁ a⟶b) (⊗₁ a⟶c) =
  let d , b⟶d , c⟶d = ⟶ʳ-weakly-confluent a⟶b a⟶c
  in (d ⊗ _) , ⊗₁* b⟶d , ⊗₁* c⟶d
⟶ʳ-weakly-confluent (⊗₁ a⟶b) (⊗₂ a⟶c) =
  _ , ⊗₂ a⟶c ◅ ⊘ , ⊗₁ a⟶b ◅ ⊘
⟶ʳ-weakly-confluent (⊗₂ a⟶b) (⊗₁ a⟶c) =
  _ , ⊗₁ a⟶c ◅ ⊘ , ⊗₂ a⟶b ◅ ⊘
⟶ʳ-weakly-confluent (⊗₂ a⟶b) (⊗₂ a⟶c) =
  let d , b⟶d , c⟶d = ⟶ʳ-weakly-confluent a⟶b a⟶c
  in (_ ⊗ d) , ⊗₂* b⟶d , ⊗₂* c⟶d
⟶ʳ-weakly-confluent (⨾₁ a⟶b) (⨾₁ a⟶c) =
  let d , b⟶d , c⟶d = ⟶ʳ-weakly-confluent a⟶b a⟶c
  in (d ⨾ _) , ⨾₁* b⟶d , ⨾₁* c⟶d
⟶ʳ-weakly-confluent (⨾₁ a⟶b) (⨾₂ a⟶c) =
  _ , ⨾₂ a⟶c ◅ ⊘ , ⨾₁ a⟶b ◅ ⊘
⟶ʳ-weakly-confluent (⨾₂ a⟶b) (⨾₁ a⟶c) =
  _ , ⨾₁ a⟶c ◅ ⊘ , ⨾₂ a⟶b ◅ ⊘
⟶ʳ-weakly-confluent (⨾₂ a⟶b) (⨾₂ a⟶c) =
  let d , b⟶d , c⟶d = ⟶ʳ-weakly-confluent a⟶b a⟶c
  in (_ ⨾ d) , ⨾₂* b⟶d , ⨾₂* c⟶d


ε⊗ε⁺-nfʳ : IsNormalForm (_⟶ʳ_) (ε⁺ ⊗ ε⁺)
ε⊗ε⁺-nfʳ (_ , ⊗₁ ())
ε⊗ε⁺-nfʳ (_ , ⊗₂ ())

ε⊗ε⁻-nfʳ : IsNormalForm (_⟶ʳ_) (ε⁻ ⊗ ε⁻)
ε⊗ε⁻-nfʳ (_ , ⊗₁ ())
ε⊗ε⁻-nfʳ (_ , ⊗₂ ())

id-nfʳ : ∀ {i : ℕ} → IsNormalForm (_⟶ʳ_) (id {i})
id-nfʳ ()

τ-nfʳ : IsNormalForm (_⟶ʳ_) τ
τ-nfʳ ()

ζζτδδ-nfʳ : IsNormalForm (_⟶ʳ_) (ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺)
ζζτδδ-nfʳ (_ , ⨾₁ (⨾₁ (⊗₁ ())))
ζζτδδ-nfʳ (_ , ⨾₁ (⨾₁ (⊗₂ ())))
ζζτδδ-nfʳ (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₁ ()))))
ζζτδδ-nfʳ (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₂ ()))))
ζζτδδ-nfʳ (_ , ⨾₂ (⊗₁ ()))
ζζτδδ-nfʳ (_ , ⨾₂ (⊗₂ ()))

δδτζζ-nfʳ : IsNormalForm (_⟶ʳ_) (δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺)
δδτζζ-nfʳ (_ , ⨾₁ (⨾₁ (⊗₁ ())))
δδτζζ-nfʳ (_ , ⨾₁ (⨾₁ (⊗₂ ())))
δδτζζ-nfʳ (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₁ ()))))
δδτζζ-nfʳ (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₂ ()))))
δδτζζ-nfʳ (_ , ⨾₂ (⊗₁ ()))
δδτζζ-nfʳ (_ , ⨾₂ (⊗₂ ()))

module _ where
  open import Induction.WellFounded
  import Relation.Binary.Construct.Closure.Transitive as Transitive
  open import Function.Bundles using (Equivalence)
  open Transitive hiding (wellFounded)

  private
    _<_ : Rel (Net i o) 0ℓ
    a < b = b ⟶ʳ a

    _⟶ʳ⁺_ : Rel (Net i o) 0ℓ
    _⟶ʳ⁺_ = Plus _⟶ʳ_

    _<⁺_ : Rel (Net i o) 0ℓ
    _<⁺_ = Plus _<_

    ⊗-acc :
        Acc _<_ a
      → Acc _<_ b
      → Acc _<_ (a ⊗ b)
    ⊗-acc (acc rs₁) (acc rs₂) =
      acc (λ{(⊗₁ y<n) → ⊗-acc (rs₁ y<n) (acc rs₂)
            ;(⊗₂ y<n) → ⊗-acc (acc rs₁) (rs₂ y<n)})
    
    mutual
      ⨾-acc :
          Acc _<_ a
        → Acc _<_ b
        → Acc _<_ (a ⨾ b)
      ⨾-acc (acc rs₁) (acc rs₂) =
        acc λ{ε-δ → <-acc _ ε-δ
            ; ε-ζ → <-acc _ ε-ζ
            ; ε-ε → <-acc _ ε-ε
            ; δ-ε → <-acc _ δ-ε
            ; ζ-ε → <-acc _ ζ-ε
            ; δ-δ → <-acc _ δ-δ
            ; ζ-ζ → <-acc _ ζ-ζ
            ; δ-ζ → <-acc _ δ-ζ
            ; ζ-δ → <-acc _ ζ-δ
            ; (⨾₁ y<n) → ⨾-acc (rs₁ y<n) (acc rs₂)
            ; (⨾₂ y<n) → ⨾-acc (acc rs₁) (rs₂ y<n)}

      <-acc : ∀ {i o : ℕ} n {y} → y < n → Acc _<_ y
      <-acc .(ε⁺ ⨾ δ⁻) {.(ε⁺ ⊗ ε⁺)} ε-δ = acc (λ x → ⊥-elim (ε⊗ε⁺-nfʳ (_ , x)))
      <-acc .(ε⁺ ⨾ ζ⁻) {.(ε⁺ ⊗ ε⁺)} ε-ζ = acc (λ x → ⊥-elim (ε⊗ε⁺-nfʳ (_ , x)))
      <-acc .(ε⁺ ⨾ ε⁻) {.id₀} ε-ε = acc (λ x → ⊥-elim (id-nfʳ (_ , x)))
      <-acc .(δ⁺ ⨾ ε⁻) {.(ε⁻ ⊗ ε⁻)} δ-ε = acc (λ x → ⊥-elim (ε⊗ε⁻-nfʳ (_ , x)))
      <-acc .(ζ⁺ ⨾ ε⁻) {.(ε⁻ ⊗ ε⁻)} ζ-ε = acc (λ x → ⊥-elim (ε⊗ε⁻-nfʳ (_ , x)))
      <-acc .(δ⁺ ⨾ δ⁻) {.τ} δ-δ = acc (λ x → ⊥-elim (τ-nfʳ (_ , x)))
      <-acc .(ζ⁺ ⨾ ζ⁻) {.τ} ζ-ζ = acc (λ x → ⊥-elim (τ-nfʳ (_ , x)))
      <-acc .(δ⁺ ⨾ ζ⁻) {.(ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺)} δ-ζ = acc (λ x → ⊥-elim (ζζτδδ-nfʳ (_ , x)))
      <-acc .(ζ⁺ ⨾ δ⁻) {.(δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺)} ζ-δ = acc (λ x → ⊥-elim (δδτζζ-nfʳ (_ , x)))
      <-acc (n₁ ⊗ n₂) {.(y₁ ⊗ n₂)} (⊗₁ {b = y₁} y₁<n₁) = ⊗-acc (<-acc n₁ y₁<n₁) (<-wf n₂)
      <-acc (n₁ ⊗ n₂) {.(n₁ ⊗ y₂)} (⊗₂ {b = y₂} y₂<n₂) = ⊗-acc (<-wf n₁) (<-acc n₂ y₂<n₂)
      <-acc (n₁ ⨾ n₂) {.(y₁ ⨾ n₂)} (⨾₁ {b = y₁} y₁<n₁) = ⨾-acc (<-acc n₁ y₁<n₁) (<-wf n₂)
      <-acc (n₁ ⨾ n₂) {.(n₁ ⨾ y₂)} (⨾₂ {b = y₂} y₂<n₂) = ⨾-acc (<-wf n₁) (<-acc n₂ y₂<n₂)

      <-wf : WellFounded (_<_ {i} {o})
      <-wf {i} {o} n = acc (<-acc {i} {o} n)
  
  <*-wf : WellFounded (TransClosure (_<_ {i} {o}))
  <*-wf {i} {o} = Transitive.wellFounded (_<_ {i} {o}) <-wf

  <⁺-wf : WellFounded (_<⁺_ {i} {o})
  <⁺-wf {i} {o} = Subrelation.wellFounded (λ {x} {y} rel → plus→trans rel) (<*-wf {i} {o})
    where
    plus→trans : ∀ {x y} → (Plus _<_ x y) → (TransClosure _<_ x y)
    plus→trans = Equivalence.to (Transitive.equivalent {0ℓ} {Net i o} {0ℓ} {_<_ {i} {o}})
  
  ⟶ʳ-normalizing : StronglyNormalizing (_⟶ʳ_ {i} {o})
  ⟶ʳ-normalizing = <-wf

  private
    module _ {a ℓ : Level} {A : Set a} {_⟶_ : Rel A ℓ} where
      fromFlip : ∀ {x y : A} → flip (Plus _⟶_) x y → Plus (flip _⟶_) x y
      fromFlip [ y⟶x ]                 = [ y⟶x ]
      fromFlip (y⟶+z ∼⁺⟨ x∼⁺y ⟩ z⟶x) = _ ∼⁺⟨ fromFlip z⟶x ⟩ fromFlip x∼⁺y

  ⟶ʳ⁺-normalizing : StronglyNormalizing (_⟶ʳ⁺_ {i} {o})
  ⟶ʳ⁺-normalizing = Subrelation.wellFounded fromFlip <⁺-wf
 
⟶ʳ-confluent : Confluent (_⟶ʳ_ {i} {o})
⟶ʳ-confluent {i} {o} = sn&wcr⇒cr (⟶ʳ⁺-normalizing {i} {o}) ⟶ʳ-weakly-confluent
