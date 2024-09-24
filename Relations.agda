open import Level
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Data.Product using (_,_; ∃; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)
open import Relation.Binary
open import Relation.Binary.Construct.Closure.ReflexiveTransitive renaming (ε to ⊘) hiding (gmap)
open import Relation.Binary.Construct.Closure.Equivalence using (EqClosure; isEquivalence; gmap)
open import Relation.Binary.Construct.Closure.Symmetric using (SymClosure; fwd; bwd)
open import Algebra.Bundles
open import Definitions

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

infix  2 _⟶ʳ*_
_⟶ʳ*_ : Rel (Net i o) 0ℓ
_⟶ʳ*_ = Star _⟶ʳ_


infixl 1 _~′⨾_ 
data _~′⨾_ : Rel (Net i o) 0ℓ where
  ⨾-id : n ⨾ id ~′⨾ n
  id-⨾ : id ⨾ n ~′⨾ n
  ⨾-assoc : (a ⨾ b) ⨾ c ~′⨾ a ⨾ (b ⨾ c)

  -- structural transitivity
  ⊗₁ : a ~′⨾ b → a ⊗ k ~′⨾ b ⊗ k
  ⊗₂ : a ~′⨾ b → k ⊗ a ~′⨾ k ⊗ b
  ⨾₁ : a ~′⨾ b → a ⨾ k ~′⨾ b ⨾ k
  ⨾₂ : a ~′⨾ b → k ⨾ a ~′⨾ k ⨾ b

infix  2 _~′⨾*_
_~′⨾*_ : Rel (Net i o) 0ℓ
_~′⨾*_ = EqClosure _~′⨾_

⊗₁* : a ~′⨾* b → a ⊗ k ~′⨾* b ⊗ k
⊗₁* {k = k} = gmap (_⊗ k) ⊗₁

⊗₂* : a ~′⨾* b → k ⊗ a ~′⨾* k ⊗ b
⊗₂* {k = k} = gmap (k ⊗_) ⊗₂

⨾₁* : a ~′⨾* b → a ⨾ k ~′⨾* b ⨾ k
⨾₁* {k = k} = gmap (_⨾ k) ⨾₁

⨾₂* : a ~′⨾* b → k ⨾ a ~′⨾* k ⨾ b
⨾₂* {k = k} = gmap (k ⨾_) ⨾₂

⨾-Monoid : ∀ {i : ℕ} → Monoid 0ℓ 0ℓ
⨾-Monoid {i} = record
  { Carrier = Net i _
  ; _≈_ = (EqClosure _~′⨾_)
  ; _∙_ = _⨾_
  ; ε = id
  ; isMonoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence _
        ; ∙-cong = λ a b → ⨾₁* a ◅◅ ⨾₂* b }
      ; assoc = λ _ _ _ → fwd ⨾-assoc ◅ ⊘ }
    ; identity = (λ _ → fwd id-⨾ ◅ ⊘) , λ _ → fwd ⨾-id ◅ ⊘ }
  }

infixl 1 _~′⊗_ 
data _~′⊗_ : Rel (Net i o) 0ℓ where
  ⊗-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {a : Net i₁ o₁}
    → {b : Net i₂ o₂}
    → {c : Net i₃ o₃}
    → (
      (_⊗_ {{i≡}} {{o≡}}
        (a ⊗ b) c)
      ~′⊗
      (_⊗_ {{trans i≡ (+-assoc i₁ i₂ i₃)}} {{trans o≡ (+-assoc o₁ o₂ o₃)}}
        a (b ⊗ c)))
  -- ⊗-empty : {{i≡ : i ≡ i + 0}} → {{o≡ : o ≡ o + 0}} → (_⊗_ {{i≡}} {{o≡}} n (id {0}) ~′⊗ n)
  ⊗-empty : (_⊗_ {{sym (+-identityʳ i)}} {{sym (+-identityʳ o)}} n (id {0}) ~′⊗ n)
  empty-⊗ : (_⊗_ {{sym (+-identityˡ i)}} {{sym (+-identityˡ o)}} (id {0}) n ~′⊗ n)

infixl 1 _~′_ 
-- Small-step syntactical equivalence on nets
data _~′_ : Rel (Net i o) 0ℓ where
  ~⨾ : a ~′⨾ b → a ~′ b
  ~⊗ : a ~′⊗ b → a ~′ b
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

infix  3 _~_
-- Syntactical equivalence
_~_ : Rel (Net i o) 0ℓ
-- TODO: it should be EqClosure, but for ease of proof we'll keep the Star
_~_ = EqClosure _~′_
-- _~_ = Star _~′_

infix  2 _⟶_
_⟶_ : Rel (Net i o) 0ℓ
a ⟶ b = ∃ λ k → a ~ k × k ⟶ʳ b

infix  2 _⟶*_
_⟶*_ : Rel (Net i o) 0ℓ
_⟶*_ = Star _⟶_
