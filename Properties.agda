open import Level
open import Relation.Binary.Rewriting
open import Data.Product using (_,_; ∃)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘)
open import Data.Nat using (ℕ)
open import Relation.Binary using (Rel)
open import Data.Empty
open import Function.Base using (flip)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Definitions
open import Relations

module _ where
  
module WeaklyConfluent where
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
open WeaklyConfluent

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

module WellFounded where
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

      -- proves that all elements smaller than y are also accessible
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

      -- all elements are acessible
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
    module _ {A : Set} {_~_ : Rel A 0ℓ} where
      fromFlip : ∀ {x y : A} → flip (Plus _~_) x y → Plus (flip _~_) x y
      fromFlip [ y~x ] = [ y~x ]
      fromFlip (_ ∼⁺⟨ x∼⁺y ⟩ y~z) = _ ∼⁺⟨ fromFlip y~z ⟩ fromFlip x∼⁺y

  ⟶ʳ⁺-normalizing : StronglyNormalizing (_⟶ʳ⁺_ {i} {o})
  ⟶ʳ⁺-normalizing = Subrelation.wellFounded fromFlip <⁺-wf
open WellFounded

⟶ʳ-confluent : Confluent (_⟶ʳ_ {i} {o})
⟶ʳ-confluent {i} {o} = sn&wcr⇒cr (⟶ʳ⁺-normalizing {i} {o}) ⟶ʳ-weakly-confluent

⟶ʳ-unf : UniqueNormalForm (_⟶ʳ_ {i} {o})
⟶ʳ-unf = conf⇒unf ⟶ʳ-confluent 