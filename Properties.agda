open import Level
open import Relation.Binary.Rewriting
open import Data.Product using (_,_; ∃; _×_; -,_)
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘)
import Relation.Binary.Construct.Closure.ReflexiveTransitive as Star
import Relation.Binary.Construct.Closure.Symmetric as Sym
import Relation.Binary.Construct.Closure.Equivalence as Eq
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (_≟_)
open import Relation.Binary using (Rel)
open import Relation.Nullary.Negation using (¬_)
open import Data.Empty
open import Function.Base using (flip; _∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; _≢_; cong; cong₂; sym; refl)

open import Definitions
open import Relations

module _ where

module ⟶ʳ-Properties where
  ⊗₁* : a ⟶ʳ* b → a ⊗ k ⟶ʳ* b ⊗ k
  ⊗₁* = Star.gmap (_⊗ _) ⊗₁

  ⊗₂* : a ⟶ʳ* b → k ⊗ a ⟶ʳ* k ⊗ b
  ⊗₂* = Star.gmap (_ ⊗_) ⊗₂

  ⨾₁* : a ⟶ʳ* b → a ⨾ k ⟶ʳ* b ⨾ k
  ⨾₁* = Star.gmap (_⨾ _) ⨾₁

  ⨾₂* : a ⟶ʳ* b → k ⨾ a ⟶ʳ* k ⨾ b
  ⨾₂* = Star.gmap (_ ⨾_) ⨾₂

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

  NF : ∀ {i o : ℕ} → Net i o → Set
  NF {i} {o} = IsNormalForm (_⟶ʳ_ {i} {o})

  HasNF : ∀ {i o : ℕ} → Net i o → Set
  HasNF {i} {o} = HasNormalForm (_⟶ʳ_ {i} {o})

  ⊗-nf : NF a → NF b → NF (a ⊗ b)
  ⊗-nf nfᵃ _   (_ , ⊗₁ ⟶ʳ) = nfᵃ (_ , ⟶ʳ)
  ⊗-nf _   nfᵇ (_ , ⊗₂ ⟶ʳ) = nfᵇ (_ , ⟶ʳ)

  -- impossible to prove
  -- ⨾-nf : NF a → NF b → NF (a ⨾ b)
  -- ⨾-nf nfᵃ _   (_ , ⨾₁ ⟶ʳ) = nfᵃ (_ , ⟶ʳ)
  -- ⨾-nf _   nfᵇ (_ , ⨾₂ ⟶ʳ) = nfᵇ (_ , ⟶ʳ)
  -- ⨾-nf nfᵃ nfᵇ (_ , ε-δ) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , ε-ζ) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (a , ε-ε) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , δ-ε) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , ζ-ε) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , δ-δ) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , ζ-ζ) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , δ-ζ) = {!   !}
  -- ⨾-nf nfᵃ nfᵇ (_ , ζ-δ) = {!   !}

  ε⁺-nf : NF ε⁺
  ε⁺-nf ()

  ε⁻-nf : NF ε⁻
  ε⁻-nf ()

  δ⁺-nf : NF δ⁺
  δ⁺-nf ()

  δ⁻-nf : NF δ⁻
  δ⁻-nf ()

  ζ⁺-nf : NF ζ⁺
  ζ⁺-nf ()

  ζ⁻-nf : NF ζ⁻
  ζ⁻-nf ()

  ε⊗ε⁺-nf : NF (ε⁺ ⊗ ε⁺)
  ε⊗ε⁺-nf = ⊗-nf ε⁺-nf ε⁺-nf

  ε⊗ε⁻-nf : NF (ε⁻ ⊗ ε⁻)
  ε⊗ε⁻-nf = ⊗-nf ε⁻-nf ε⁻-nf

  id-nf : NF (id {i})
  id-nf ()

  τ-nf : NF τ
  τ-nf ()

  ζζτδδ-nf : NF (ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺)
  ζζτδδ-nf (_ , ⨾₁ (⨾₁ (⊗₁ ())))
  ζζτδδ-nf (_ , ⨾₁ (⨾₁ (⊗₂ ())))
  ζζτδδ-nf (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₁ ()))))
  ζζτδδ-nf (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₂ ()))))
  ζζτδδ-nf (_ , ⨾₂ (⊗₁ ()))
  ζζτδδ-nf (_ , ⨾₂ (⊗₂ ()))

  δδτζζ-nf : NF (δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺)
  δδτζζ-nf (_ , ⨾₁ (⨾₁ (⊗₁ ())))
  δδτζζ-nf (_ , ⨾₁ (⨾₁ (⊗₂ ())))
  δδτζζ-nf (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₁ ()))))
  δδτζζ-nf (_ , ⨾₁ (⨾₂ (⊗₁ (⊗₂ ()))))
  δδτζζ-nf (_ , ⨾₂ (⊗₁ ()))
  δδτζζ-nf (_ , ⨾₂ (⊗₂ ()))

  module WellFounded where
    open import Induction.WellFounded
    import Relation.Binary.Construct.Closure.Transitive as Transitive
    open import Function.Bundles using (Equivalence)
    open Transitive hiding (wellFounded)

    _<_ : Rel (Net i o) 0ℓ
    _<_ = flip _⟶ʳ_

    module _ {A : Set} {_⟶_ : Rel A 0ℓ} where
      fromFlip : ∀ {x y : A} → flip (Plus _⟶_) x y → Plus (flip _⟶_) x y
      fromFlip [ y⟶x ] = [ y⟶x ]
      fromFlip (_ ∼⁺⟨ x∼⁺y ⟩ y⟶z) = _ ∼⁺⟨ fromFlip y⟶z ⟩ fromFlip x∼⁺y

      -- open All
      -- sn⇒wn : StronglyNormalizing (_⟶_) → WeaklyNormalizing (_⟶_)
      -- -- sn⇒wn sn n with sn n
      -- -- ... | acc asd = {!   !} , ({!   !} , {!   !})
      -- sn⇒wn sn n with sn n 
      -- ... | acc asd = dls n
      --   where
      --     dls = wfRec sn _ (λ x → HasNormalForm (_⟶_) x) λ a b → go a λ y → b
      --       where
      --       go : ∀ x → (∀ y → x ⟶ y → (HasNormalForm (_⟶_) y)) → (HasNormalForm (_⟶_) x)
      --       go x rec = rec {!   !} {!   !}

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
      <-acc .(ε⁺ ⨾ δ⁻) {.(ε⁺ ⊗ ε⁺)} ε-δ = acc (λ x → ⊥-elim (ε⊗ε⁺-nf (_ , x)))
      <-acc .(ε⁺ ⨾ ζ⁻) {.(ε⁺ ⊗ ε⁺)} ε-ζ = acc (λ x → ⊥-elim (ε⊗ε⁺-nf (_ , x)))
      <-acc .(ε⁺ ⨾ ε⁻) {.id₀} ε-ε = acc (λ x → ⊥-elim (id-nf (_ , x)))
      <-acc .(δ⁺ ⨾ ε⁻) {.(ε⁻ ⊗ ε⁻)} δ-ε = acc (λ x → ⊥-elim (ε⊗ε⁻-nf (_ , x)))
      <-acc .(ζ⁺ ⨾ ε⁻) {.(ε⁻ ⊗ ε⁻)} ζ-ε = acc (λ x → ⊥-elim (ε⊗ε⁻-nf (_ , x)))
      <-acc .(δ⁺ ⨾ δ⁻) {.τ} δ-δ = acc (λ x → ⊥-elim (τ-nf (_ , x)))
      <-acc .(ζ⁺ ⨾ ζ⁻) {.τ} ζ-ζ = acc (λ x → ⊥-elim (τ-nf (_ , x)))
      <-acc .(δ⁺ ⨾ ζ⁻) {.(ζ⁻ ⊗ ζ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ δ⁺ ⊗ δ⁺)} δ-ζ = acc (λ x → ⊥-elim (ζζτδδ-nf (_ , x)))
      <-acc .(ζ⁺ ⨾ δ⁻) {.(δ⁻ ⊗ δ⁻ ⨾ id₁ ⊗ τ ⊗ id₁ ⨾ ζ⁺ ⊗ ζ⁺)} ζ-δ = acc (λ x → ⊥-elim (δδτζζ-nf (_ , x)))
      <-acc (n₁ ⊗ n₂) {_} (⊗₁ {b = y₁} y₁<n₁) = ⊗-acc (<-acc n₁ y₁<n₁) (<-wf n₂)
      <-acc (n₁ ⊗ n₂) {_} (⊗₂ {b = y₂} y₂<n₂) = ⊗-acc (<-wf n₁) (<-acc n₂ y₂<n₂)
      <-acc (n₁ ⨾ n₂) {.(y₁ ⨾ n₂)} (⨾₁ {b = y₁} y₁<n₁) = ⨾-acc (<-acc n₁ y₁<n₁) (<-wf n₂)
      <-acc (n₁ ⨾ n₂) {.(n₁ ⨾ y₂)} (⨾₂ {b = y₂} y₂<n₂) = ⨾-acc (<-wf n₁) (<-acc n₂ y₂<n₂)

      -- all elements are acessible
      <-wf : WellFounded (_<_ {i} {o})
      <-wf {i} {o} n = acc (<-acc {i} {o} n)
    
      <*-wf : WellFounded (TransClosure (_<_ {i} {o}))
      <*-wf {i} {o} = Transitive.wellFounded (_<_ {i} {o}) <-wf

      <⁺-wf : WellFounded (Plus (_<_ {i} {o}))
      <⁺-wf {i} {o} = Subrelation.wellFounded (λ {x} {y} rel → plus→trans rel) (<*-wf {i} {o})
        where
        plus→trans : ∀ {x y} → (Plus _<_ x y) → (TransClosure _<_ x y)
        plus→trans = Equivalence.to (Transitive.equivalent {0ℓ} {Net i o} {0ℓ} {_<_ {i} {o}})
    
    ⟶ʳ-normalizing : StronglyNormalizing (_⟶ʳ_ {i} {o})
    ⟶ʳ-normalizing = <-wf

    ⟶ʳ⁺-normalizing : StronglyNormalizing (Plus (_⟶ʳ_ {i} {o}))
    ⟶ʳ⁺-normalizing = Subrelation.wellFounded fromFlip <⁺-wf

    -- reduce : (a : Net i o) → ∃ λ b → (NF b) × (a ⟶ʳ* b)
    -- reduce a = {!   !}

  open WellFounded

  ⟶ʳ-confluent : Confluent (_⟶ʳ_ {i} {o})
  ⟶ʳ-confluent {i} {o} = sn&wcr⇒cr (⟶ʳ⁺-normalizing {i} {o}) ⟶ʳ-weakly-confluent

  ⟶ʳ-unf : UniqueNormalForm (_⟶ʳ_ {i} {o})
  ⟶ʳ-unf = conf⇒unf ⟶ʳ-confluent

  data Progress {i o : ℕ} (a : Net i o) : Set where
    step : ∀ {b : Net i o} → a ⟶ʳ b → Progress a
    done : NF a → Progress a

  ⟶ʳ-progress : ∀ (n : Net i o) → Progress {i} {o} n
  ⟶ʳ-progress id = done id-nf
  ⟶ʳ-progress τ = done τ-nf
  ⟶ʳ-progress ε⁺ = done ε⁺-nf
  ⟶ʳ-progress ε⁻ = done ε⁻-nf
  ⟶ʳ-progress δ⁺ = done δ⁺-nf
  ⟶ʳ-progress δ⁻ = done δ⁻-nf
  ⟶ʳ-progress ζ⁺ = done ζ⁺-nf
  ⟶ʳ-progress ζ⁻ = done ζ⁻-nf
  ⟶ʳ-progress (_⊗_ {{refl}} {{refl}} a b) with ⟶ʳ-progress a
  ... | step {a′} a⟶a′ = step (⊗₁ a⟶a′)
  ... | done a-nf with ⟶ʳ-progress b
  ... | step b⟶b′ = step (⊗₂ b⟶b′)
  ... | done b-nf = done (⊗-nf a-nf b-nf)
  ⟶ʳ-progress (a ⨾ b) with ⟶ʳ-progress a
  ... | step {a′} a⟶a′ = step (⨾₁ a⟶a′)
  ... | done a-nf with ⟶ʳ-progress b
  ... | step b⟶b′ = step (⨾₂ b⟶b′)
  ⟶ʳ-progress (id ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (τ ⨾ b)  | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (a ⨾ id) | done a-nf | done b-nf = done (λ{(_ , ⨾₁ a⟶) → a-nf (_ , a⟶)})
  ⟶ʳ-progress (a ⨾ τ)  | done a-nf | done b-nf = done (λ{(_ , ⨾₁ a⟶) → a-nf (_ , a⟶)})
  
  ⟶ʳ-progress (ε⁺ ⨾ ε⁻) | done a-nf | done b-nf = step ε-ε
  ⟶ʳ-progress (ε⁺ ⨾ δ⁻) | done a-nf | done b-nf = step ε-δ
  ⟶ʳ-progress (ε⁺ ⨾ ζ⁻) | done a-nf | done b-nf = step ε-ζ
  ⟶ʳ-progress (δ⁺ ⨾ ε⁻) | done a-nf | done b-nf = step δ-ε
  ⟶ʳ-progress (δ⁺ ⨾ δ⁻) | done a-nf | done b-nf = step δ-δ
  ⟶ʳ-progress (δ⁺ ⨾ ζ⁻) | done a-nf | done b-nf = step δ-ζ
  ⟶ʳ-progress (ζ⁺ ⨾ ε⁻) | done a-nf | done b-nf = step ζ-ε
  ⟶ʳ-progress (ζ⁺ ⨾ δ⁻) | done a-nf | done b-nf = step ζ-δ
  ⟶ʳ-progress (ζ⁺ ⨾ ζ⁻) | done a-nf | done b-nf = step ζ-ζ

  ⟶ʳ-progress (ε⁺ ⨾ (b₁ ⊗ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (ε⁺ ⨾ (b₁ ⨾ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (δ⁺ ⨾ (b₁ ⊗ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (δ⁺ ⨾ (b₁ ⨾ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (ζ⁺ ⨾ (b₁ ⊗ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (ζ⁺ ⨾ (b₁ ⨾ b₂)) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})

  ⟶ʳ-progress (ε⁻ ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (δ⁻ ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (ζ⁻ ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (a₁ ⊗ a₂ ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₁ a⟶) → a-nf (_ , a⟶)
                                                              ;(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})
  ⟶ʳ-progress (a₁ ⨾ a₂ ⨾ b) | done a-nf | done b-nf = done (λ{(_ , ⨾₁ a⟶) → a-nf (_ , a⟶)
                                                              ;(_ , ⨾₂ b⟶) → b-nf (_ , b⟶)})

  reduce : ∀ (a : Net i o) → HasNF a
  reduce = wfRec _ _ go
    where
      import Induction.WellFounded
      open Induction.WellFounded.All ⟶ʳ-normalizing
      go : ∀ (x : Net i o) → (∀ {y} → x ⟶ʳ y → HasNF y) → HasNF x
      go x rec with ⟶ʳ-progress x
      ... | done x-nf = x , x-nf , ⊘
      ... | step x⟶y =
        let z , z-nf , y⟶*z = rec x⟶y
        in z , z-nf , x⟶y ◅ y⟶*z
  
open Sym
-- all symmetric relations are weakly-confluent
rel-weakly-confluent : ∀ {A : Set} → {_⟶_ : Rel A 0ℓ} → WeaklyConfluent (SymClosure _⟶_)
rel-weakly-confluent a⟶b a⟶c with a⟶b | a⟶c
... | fwd a⟶b | fwd a⟶c = _ , ((bwd a⟶b ◅ ⊘) , ((bwd a⟶c ◅ ⊘)))
... | fwd a⟶b | bwd c⟶a = _ , (⊘ , fwd c⟶a ◅ fwd a⟶b ◅ ⊘)
... | bwd b⟶a | fwd a⟶c = _ , (fwd b⟶a ◅ fwd a⟶c ◅ ⊘ , ⊘)
... | bwd b⟶a | bwd c⟶a = _ , (fwd b⟶a ◅ ⊘ , fwd c⟶a ◅ ⊘)

-- there exists some nets which are in normal form in ⟶ʳ but not in ⟶
∃-nfʳ¬nf : ∃ λ a → ∃ λ b → (¬ (a ⟶ʳ b)) × (a ⟶ b)
∃-nfʳ¬nf =
  let a = (ε⁺ ⨾ id ⨾ ε⁻)
      b = id₀
      nfʳ = λ()
      a⟶b = ε⁺ ⨾ ε⁻ , fwd (⨾₁ ⨾-id) ◅ ⊘ , ε-ε
  in a , b , nfʳ , a⟶b

module ~-Properties where
  ⊗₁* : a ~ b → a ⊗ k ~ b ⊗ k
  ⊗₁* {k = k} = Eq.gmap (_⊗ k) ⊗₁

  ⊗₂* : a ~ b → k ⊗ a ~ k ⊗ b
  ⊗₂* {k = k} = Eq.gmap (k ⊗_) ⊗₂

  ⨾₁* : a ~ b → a ⨾ k ~ b ⨾ k
  ⨾₁* {k = k} = Eq.gmap (_⨾ k) ⨾₁

  ⨾₂* : a ~ b → k ⨾ a ~ k ⨾ b
  ⨾₂* {k = k} = Eq.gmap (k ⨾_) ⨾₂

  open import Relation.Nullary using (Dec; yes; no)

  data Raw : Set where
    id : {ℕ} → Raw
    τ : Raw
    ε⁺ ε⁻ δ⁺ δ⁻ ζ⁺ ζ⁻ : Raw
    _⊗_ _⨾_ : Raw → Raw → Raw

  erase : Net i o → Raw
  erase {i} id = id {i}
  erase τ = τ
  erase ε⁺ = ε⁺
  erase ε⁻ = ε⁻
  erase δ⁺ = δ⁺
  erase δ⁻ = δ⁻
  erase ζ⁺ = ζ⁺
  erase ζ⁻ = ζ⁻
  erase (a ⊗ b) = erase a ⊗ erase b
  erase (a ⨾ b) = erase a ⨾ erase b

  data Infer : Raw → Set where
    ok : (n : Net i o) → Infer (erase n)
    bad : {e : Raw} → Infer e

  infer : (e : Raw) -> Infer e
  infer id = ok id
  infer τ = ok τ
  infer ε⁺ = ok ε⁺
  infer ε⁻ = ok ε⁻
  infer δ⁺ = ok δ⁺
  infer δ⁻ = ok δ⁻
  infer ζ⁺ = ok ζ⁺
  infer ζ⁻ = ok ζ⁻
  infer (x ⊗ y) with infer x | infer y
  ... | bad | bad = bad
  ... | _   | bad = bad
  ... | bad | _ = bad
  ... | ok {i₁} {o₁} x′ | ok {i₂} {o₂} y′ = ok (_⊗_  x′ y′)
  infer (a ⨾ b) with infer a | infer b
  ... | bad | bad = bad
  ... | _   | bad = bad
  ... | bad | _ = bad
  ... | ok {i₁} {o₁} a′ | ok {i₂} {o₂} b′ with o₁ ≟ i₂
  ... | no _ = bad
  ... | yes refl = ok (a′ ⨾ b′)

  erase-infer≡ok : ∀ (n : Net i o) → infer (erase n) ≡ ok n
  erase-infer≡ok id = refl
  erase-infer≡ok τ = refl
  erase-infer≡ok ε⁺ = refl
  erase-infer≡ok ε⁻ = refl
  erase-infer≡ok δ⁺ = refl
  erase-infer≡ok δ⁻ = refl
  erase-infer≡ok ζ⁺ = refl
  erase-infer≡ok ζ⁻ = refl
  erase-infer≡ok (_⊗_ {{i≡}} {{o≡}} a b)
    with infer (erase a) | infer (erase b) | erase-infer≡ok a | erase-infer≡ok b
  ... | ok a′ | ok b′ | refl | refl rewrite i≡ | o≡ = refl
  erase-infer≡ok (a ⨾ b)
    with infer (erase a) | infer (erase b) | erase-infer≡ok a | erase-infer≡ok b
  ... | ok {i₁} {o₁} a′ | ok {i₂} {o₂} b′ | refl | refl with o₁ ≟ i₂
  ... | no ¬x = ⊥-elim (¬x refl)
  ... | yes refl = refl


module ⟶-Properties where
  open ~-Properties renaming (⊗₁* to ~-⊗₁*; ⊗₂* to ~-⊗₂*; ⨾₁* to ~-⨾₁*; ⨾₂* to ~-⨾₂*)
  -- open ⟶ʳ-Properties hiding (⊗₁*; ⊗₂*; ⨾₁*; ⨾₂*)
  open ⟶ʳ-Properties.WeaklyConfluent

  ⊗₁* : a ⟶* b → a ⊗ k ⟶* b ⊗ k
  ⊗₁* {k = k} = Star.gmap (_⊗ k) λ{(x , (a~x , x⟶a′)) → x ⊗ k ,  ~-⊗₁* a~x , ⊗₁ x⟶a′}

  ⊗₂* : a ⟶* b → k ⊗ a ⟶* k ⊗ b
  ⊗₂* {k = k} = Star.gmap (k ⊗_) λ{(x , (a~x , x⟶a′)) → k ⊗ x ,  ~-⊗₂* a~x , ⊗₂ x⟶a′}

  ⨾₁* : a ⟶* b → a ⨾ k ⟶* b ⨾ k
  ⨾₁* {k = k} = Star.gmap (_⨾ k) λ{(x , (a~x , x⟶a′)) → x ⨾ k ,  ~-⨾₁* a~x , ⨾₁ x⟶a′}

  ⨾₂* : a ⟶* b → k ⨾ a ⟶* k ⨾ b
  ⨾₂* {k = k} = Star.gmap (k ⨾_) λ{(x , (a~x , x⟶a′)) → k ⨾ x ,  ~-⨾₂* a~x , ⨾₂ x⟶a′}

  -- ⟶-weakly-confluent : WeaklyConfluent (_⟶_ {i} {o})
  -- ⟶-weakly-confluent {A = a} {B = b} {C = c} (b′ , a~b′ , b′⟶ʳb) (c′ , a~c′ , c′⟶ʳc) =
  --   let asd = ⟶ʳ-weakly-confluent {!   !} {!   !}
  --   in b , (⊘ , {!   !})

  -- module WellFounded where
  --   open import Induction.WellFounded
  --   open ⟶ʳ-Properties.WellFounded

  --   private
  --     _⟵_ : Rel (Net i o) 0ℓ
  --     _⟵_ = flip _⟶_
      
  --     mutual
  --       -- proves that all elements smaller than y are also accessible
  --       ⟵-acc : ∀ {i o : ℕ} n {y} → y ⟵ n → Acc _⟵_ y
  --       ⟵-acc n {y} (x , (n~x , x⟶ʳy)) =
  --         let asd = <-acc _ x⟶ʳy
  --         in {!   !}

  --       -- all elements are acessible
  --       ⟵-wf : WellFounded (_⟵_ {i} {o})
  --       ⟵-wf {i} {o} n = acc (⟵-acc {i} {o} n)

  --   ⟶-normalizing : StronglyNormalizing (_⟶_ {i} {o})
  --   ⟶-normalizing = ⟵-wf
 
  