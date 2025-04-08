------------------------------------------------------------------------
-- The zero-one-twice-many modality
------------------------------------------------------------------------

-- Based on Conor McBride's "I Got Plenty o’ Nuttin’".

-- It might make sense to replace some of the proofs with automated
-- proofs.

open import Tools.Bool using (Bool; true; false; if_then_else_; T)

module Modality
  -- -- Should 𝟙 be below 𝟘?
  -- (𝟙≤𝟘 : Bool)
  where

𝟙≤𝟘 : Bool
𝟙≤𝟘 = true

import Tools.Algebra
open import Tools.Empty
open import Tools.Function
open import Tools.Level
open import Tools.Nat using (1+; Sequence)
open import Tools.Product
open import Tools.PropositionalEquality as PE
import Tools.Reasoning.PartialOrder
import Tools.Reasoning.PropositionalEquality
open import Tools.Relation
open import Tools.Sum using (_⊎_; inj₁; inj₂)

import Graded.Modality
import Graded.Modality.Instances.LowerBounded as LowerBounded
import Graded.Modality.Properties.Addition as Addition
import Graded.Modality.Properties.Greatest-lower-bound as GLB
import Graded.Modality.Properties.Meet as Meet
import Graded.Modality.Properties.Multiplication as Multiplication
import Graded.Modality.Properties.PartialOrder as PartialOrder
import Graded.Modality.Properties.Star as Star
import Graded.Modality.Properties.Natrec as Natrec
import Graded.Modality.Properties.Subtraction as Subtraction

------------------------------------------------------------------------
-- The type

-- Zero, one or many.

data Zero-one-twice-many : Set where
  𝟘 𝟙 𝟚 ω : Zero-one-twice-many

private variable
  n n₁ n₂ p p₁ p₂ q r result s s₁ s₂ z z₁ z₂ : Zero-one-twice-many

open Graded.Modality Zero-one-twice-many
open Tools.Algebra   Zero-one-twice-many

-- A decision procedure for equality.

infix 10 _≟_

_≟_ : Decidable (_≡_ {A = Zero-one-twice-many})
𝟘 ≟ 𝟘 = yes refl
𝟘 ≟ 𝟙 = no (λ ())
𝟘 ≟ 𝟚 = no (λ ())
𝟘 ≟ ω = no (λ ())
𝟙 ≟ 𝟘 = no (λ ())
𝟙 ≟ 𝟙 = yes refl
𝟙 ≟ 𝟚 = no (λ ())
𝟙 ≟ ω = no (λ ())
𝟚 ≟ 𝟘 = no (λ ())
𝟚 ≟ 𝟙 = no (λ ())
𝟚 ≟ 𝟚 = yes refl
𝟚 ≟ ω = no (λ ())
ω ≟ 𝟘 = no (λ ())
ω ≟ 𝟙 = no (λ ())
ω ≟ 𝟚 = no (λ ())
ω ≟ ω = yes refl

------------------------------------------------------------------------
-- Meet

-- Some requirements of a meet operation.

Meet-requirements :
  (Zero-one-twice-many → Zero-one-twice-many → Zero-one-twice-many) → Set
Meet-requirements _∧_ =
  (𝟘 ∧ 𝟘 ≡ 𝟘) ×
  (𝟙 ∧ 𝟙 ≡ 𝟙) ×
  (ω ∧ ω ≡ ω) ×
  (𝟘 ∧ ω ≡ ω) ×
  (ω ∧ 𝟘 ≡ ω) ×
  (𝟙 ∧ ω ≡ ω) ×
  (ω ∧ 𝟙 ≡ ω) ×
  (𝟘 ∧ 𝟙 ≢ 𝟘) ×
  (𝟙 ∧ 𝟘 ≢ 𝟘)

-- The meet operation of a "Semiring-with-meet" for Zero-one-twice-many for
-- which the zero is 𝟘, the one is 𝟙, ω ≤ p for all p
-- and 𝟘 ∧ 𝟙 ≢ 𝟘 has to satisfy the Meet-requirements.

Meet-requirements-required :
  (M : Semiring-with-meet) →
  Semiring-with-meet.𝟘          M ≡ 𝟘 →
  Semiring-with-meet.𝟙          M ≡ 𝟙 →
  Semiring-with-meet._∧_ M    𝟘 𝟙 ≢ 𝟘 →
  (∀ p → Semiring-with-meet._≤_ M ω p) →
  Meet-requirements (Semiring-with-meet._∧_ M)
Meet-requirements-required M@record{} refl refl 𝟙≢𝟘 ω≤ =
    (𝟘 ∧ 𝟘  ≡⟨ ∧-idem _ ⟩
     𝟘      ∎)
  , (𝟙 ∧ 𝟙  ≡⟨ ∧-idem _ ⟩
     𝟙      ∎)
  , (ω ∧ ω  ≡⟨ ∧-idem _ ⟩
     ω      ∎)
  , (𝟘 ∧ ω  ≡⟨ ∧-comm _ _ ⟩
     ω ∧ 𝟘  ≡˘⟨ ω≤ 𝟘 ⟩
     ω      ∎)
  , (ω ∧ 𝟘  ≡˘⟨ ω≤ 𝟘 ⟩
     ω      ∎)
  , (𝟙 ∧ ω  ≡⟨ ∧-comm _ _ ⟩
     ω ∧ 𝟙  ≡˘⟨ ω≤ 𝟙 ⟩
     ω      ∎)
  , (ω ∧ 𝟙  ≡˘⟨ ω≤ 𝟙 ⟩
     ω      ∎)
  , 𝟙≢𝟘
  , (λ 𝟙∧𝟘≡𝟘 → 𝟙≢𝟘 (
       𝟘 ∧ 𝟙  ≡⟨ ∧-comm _ _ ⟩
       𝟙 ∧ 𝟘  ≡⟨ 𝟙∧𝟘≡𝟘 ⟩
       𝟘      ∎))
  where
  open Semiring-with-meet M hiding (𝟘; 𝟙; ω)
  open Meet M
  open PartialOrder M
  open Tools.Reasoning.PropositionalEquality

-- The result of 𝟘 ∧ 𝟙 and 𝟙 ∧ 𝟘.

-- Meet.

infixr 43 _∧_

_∧_ : Zero-one-twice-many → Zero-one-twice-many → Zero-one-twice-many
𝟘 ∧ 𝟘 = 𝟘
𝟘 ∧ 𝟙 = 𝟙
𝟙 ∧ 𝟘 = 𝟙
𝟙 ∧ 𝟙 = 𝟙
𝟚 ∧ 𝟚 = 𝟚
ω ∧ _ = ω
_ ∧ ω = ω
_ ∧ _ = 𝟚

-- If 𝟙≤𝟘 is false, then 𝟙 ≡ ω.

𝟙≡ω : ¬ T 𝟙≤𝟘 → 𝟙 ≡ ω
𝟙≡ω = lemma _
  where
  lemma : ∀ b → ¬ T b → (if b then 𝟙 else ω) ≡ ω
  lemma false _  = refl
  lemma true  ¬⊤ = ⊥-elim (¬⊤ _)

-- If 𝟙 ≢ 𝟙, then 𝟙≤𝟘 is false.

𝟙≢𝟙→𝟙≰𝟘 : 𝟙 ≢ 𝟙 → ¬ T 𝟙≤𝟘
𝟙≢𝟙→𝟙≰𝟘 = lemma _
  where
  lemma : ∀ b → (if b then 𝟙 else ω) ≢ 𝟙 → ¬ T b
  lemma true  𝟙≢𝟙 = λ _ → 𝟙≢𝟙 refl
  lemma false _   = idᶠ

-- The value of 𝟙 is not 𝟘.

𝟙≢𝟘 : 𝟙 ≢ 𝟘
𝟙≢𝟘 = lemma _
  where
  lemma : ∀ b → (if b then 𝟙 else ω) ≢ 𝟘
  lemma false ()
  lemma true  ()

-- One can prove that something holds for 𝟙 by proving that it holds
-- for 𝟙 (under the assumption that 𝟙 is 𝟙), and that it holds for ω
-- (under the assumption that 𝟙 is ω).

𝟙-elim :
  ∀ {p} (P : Zero-one-twice-many → Set p) →
  (𝟙 ≡ 𝟙 → P 𝟙) →
  (𝟙 ≡ ω → P ω) →
  P 𝟙
𝟙-elim P one omega = lemma _ refl
  where
  lemma : ∀ p → 𝟙 ≡ p → P p
  lemma 𝟘 𝟙≡𝟘 = ⊥-elim (𝟙≢𝟘 𝟙≡𝟘)
  lemma 𝟙 𝟙≡𝟙 = one 𝟙≡𝟙
  lemma 𝟚 ()
  lemma ω 𝟙≡ω = omega 𝟙≡ω

-- 𝟘 ∧ 𝟙 is equal to 𝟙.

𝟘∧[𝟙] : 𝟘 ∧ 𝟙 ≡ 𝟙
𝟘∧[𝟙] = 𝟙-elim
  (λ p → 𝟘 ∧ p ≡ p)
  (λ 𝟙≡𝟙 → 𝟙≡𝟙)
  (λ _ → refl)

-- 𝟙 ∧ 𝟙 is equal to 𝟙.

𝟙∧[𝟙] : 𝟙 ∧ 𝟙 ≡ 𝟙
𝟙∧[𝟙] = 𝟙-elim
  (λ p → 𝟙 ∧ p ≡ p)
  (λ _ → refl)
  (λ _ → refl)

-- The value ω is a right zero for _∧_.

∧-zeroʳ : RightZero ω _∧_
∧-zeroʳ 𝟘 = refl
∧-zeroʳ 𝟙 = refl
∧-zeroʳ 𝟚 = refl
∧-zeroʳ ω = refl

-- -- The value ω is a zero for _∧_.

-- ∧-zero : Zero ω _∧_
-- ∧-zero = (λ _ → refl) , ∧-zeroʳ

-- If p ∧ q is 𝟙, then at least one of p and q is 𝟙, and if the other
-- one is not 𝟙, then it is 𝟘, and 𝟙 ≤ 𝟘.

∧≡𝟙 :
  p ∧ q ≡ 𝟙 →
  p ≡ 𝟘 × q ≡ 𝟙 ⊎
  p ≡ 𝟙 × q ≡ 𝟘 ⊎
  p ≡ 𝟙 × q ≡ 𝟙
∧≡𝟙 {p = 𝟘} {q = 𝟙} eq = inj₁ (refl , refl)
∧≡𝟙 {p = 𝟙} {q = 𝟘} eq = inj₂ (inj₁ (refl , refl))
∧≡𝟙 {p = 𝟙} {q = 𝟙} _  = inj₂ (inj₂ (refl , refl))
∧≡𝟙 {p = 𝟘} {q = 𝟘} ()
∧≡𝟙 {p = 𝟘} {q = ω} ()
∧≡𝟙 {p = 𝟙} {q = ω} ()
∧≡𝟙 {p = ω}         ()

opaque

  -- 𝟙 ∧ p is not equal to 𝟘

  𝟙∧p≢𝟘 : ∀ p → 𝟙 ∧ p ≢ 𝟘
  𝟙∧p≢𝟘 𝟘 = 𝟙≢𝟘
  𝟙∧p≢𝟘 𝟙 = λ ()
  𝟙∧p≢𝟘 ω = λ ()

------------------------------------------------------------------------
-- Ordering

-- Some requirements of an ordering relation.

Order-requirements : (Zero-one-twice-many → Zero-one-twice-many → Set) → Set
Order-requirements _≤_ = (ω ≤ 𝟙) × (ω ≤ 𝟘) × ¬ (𝟘 ≤ 𝟙)

-- The ordering relation of a "Semiring-with-meet" for Zero-one-twice-many for
-- which the zero is 𝟘, the one is 𝟙 and p ∧ ω equals ω for all p
-- has to satisfy the Order-requirements.

Order-requirements-required :
  (M : Semiring-with-meet) →
  Semiring-with-meet.𝟘          M ≡ 𝟘 →
  Semiring-with-meet.𝟙          M ≡ 𝟙 →
  Semiring-with-meet._∧_ M    𝟘 𝟙 ≢ 𝟘 →
  (∀ p → Semiring-with-meet._≤_ M ω p) →
  Order-requirements (Semiring-with-meet._≤_ M)
Order-requirements-required M@record{} refl refl 𝟙≢𝟘 ω≤ =
  case Meet-requirements-required M refl refl 𝟙≢𝟘 ω≤ of λ where
    (_ , _ , _ , _ , ω⊓𝟘≡ω , _ , ω⊓𝟙≡ω , 𝟘⊓𝟙≢𝟘 , _) →
        (ω      ≡˘⟨ ω⊓𝟙≡ω ⟩
         ω ⊓ 𝟙  ∎)
      , (ω      ≡˘⟨ ω⊓𝟘≡ω ⟩
         ω ⊓ 𝟘  ∎)
      , (λ 𝟘≡𝟘⊓𝟙 → 𝟘⊓𝟙≢𝟘 (
           𝟘 ⊓ 𝟙  ≡˘⟨ 𝟘≡𝟘⊓𝟙 ⟩
           𝟘      ∎))
  where
  open Semiring-with-meet M using () renaming (_∧_ to _⊓_)
  open Tools.Reasoning.PropositionalEquality

-- The inferred ordering relation.

infix 10 _≤_

_≤_ : Zero-one-twice-many → Zero-one-twice-many → Set
p ≤ q = p ≡ p ∧ q

-- The quantity ω is smaller than all others.

ω≤ : ∀ p → ω ≤ p
ω≤ _ = refl

-- 𝟘 is maximal.

𝟘-maximal : 𝟘 ≤ p → p ≡ 𝟘
𝟘-maximal {p = ω} ()
𝟘-maximal {p = 𝟘} refl = refl
𝟘-maximal {p = 𝟙}      = 𝟙-elim
  (λ q → 𝟘 ≡ q → 𝟙 ≡ 𝟘)
  (λ _ → sym)
  (λ _ ())

-- 𝟘 is not below 𝟙.

𝟘≰𝟙 : ¬ 𝟘 ≤ 𝟙
𝟘≰𝟙 = 𝟙≢𝟘 ∘→ 𝟘-maximal


opaque

  -- Non-zero grades are less than or equal to 𝟙

  ≢𝟘→≤𝟙 : ∀ p → p ≢ 𝟘 → p ≤ 𝟙
  ≢𝟘→≤𝟙 𝟘 p≢𝟘 = ⊥-elim (p≢𝟘 refl)
  ≢𝟘→≤𝟙 𝟙 p≢𝟘 = refl
  ≢𝟘→≤𝟙 𝟚 p≢𝟘 = refl
  ≢𝟘→≤𝟙 ω p≢𝟘 = refl

------------------------------------------------------------------------
-- Addition

-- Addition.

infixr 40 _+_

_+_ : Zero-one-twice-many → Zero-one-twice-many → Zero-one-twice-many
𝟘 + q = q
p + 𝟘 = p
𝟙 + 𝟙 = 𝟚
_ + _ = ω

-- If 𝟙≤𝟘 is true, then _+_ is decreasing in its left argument.

+-decreasingˡ : T 𝟙≤𝟘 → ∀ p q → p + q ≤ p
+-decreasingˡ 𝟙≤𝟘 𝟘 𝟘 = refl
+-decreasingˡ 𝟙≤𝟘 𝟘 𝟙 = refl
+-decreasingˡ 𝟙≤𝟘 𝟘 𝟚 = refl
+-decreasingˡ 𝟙≤𝟘 𝟘 ω = refl
+-decreasingˡ 𝟙≤𝟘 𝟙 𝟘 = refl
+-decreasingˡ 𝟙≤𝟘 𝟙 𝟙 = refl
+-decreasingˡ 𝟙≤𝟘 𝟙 𝟚 = refl
+-decreasingˡ 𝟙≤𝟘 𝟙 ω = refl
+-decreasingˡ 𝟙≤𝟘 𝟚 𝟘 = refl
+-decreasingˡ 𝟙≤𝟘 𝟚 𝟙 = refl
+-decreasingˡ 𝟙≤𝟘 𝟚 𝟚 = refl
+-decreasingˡ 𝟙≤𝟘 𝟚 ω = refl
+-decreasingˡ 𝟙≤𝟘 ω 𝟘 = refl
+-decreasingˡ 𝟙≤𝟘 ω 𝟙 = refl
+-decreasingˡ 𝟙≤𝟘 ω 𝟚 = refl
+-decreasingˡ 𝟙≤𝟘 ω ω = refl

-- If p + q is 𝟙, then either p is 𝟙 and q is 𝟘, or q is 𝟙 and p is 𝟘.

+≡𝟙 : p + q ≡ 𝟙 → p ≡ 𝟙 × q ≡ 𝟘 ⊎ p ≡ 𝟘 × q ≡ 𝟙
+≡𝟙 {p = 𝟘} {q = 𝟙} refl = inj₂ (refl , refl)
+≡𝟙 {p = 𝟙} {q = 𝟘} refl = inj₁ (refl , refl)
+≡𝟙 {p = 𝟘} {q = 𝟘} ()
+≡𝟙 {p = 𝟘} {q = ω} ()
+≡𝟙 {p = 𝟘} {q = 𝟚} ()
+≡𝟙 {p = 𝟙} {q = 𝟙} ()
+≡𝟙 {p = 𝟙} {q = 𝟚} ()
+≡𝟙 {p = 𝟙} {q = ω} ()
+≡𝟙 {p = ω} {q = 𝟘} ()
+≡𝟙 {p = ω} {q = 𝟙} ()
+≡𝟙 {p = ω} {q = 𝟚} ()
+≡𝟙 {p = ω} {q = ω} ()

-- The value ω is a right zero for _+_.

+-zeroʳ : RightZero ω _+_
+-zeroʳ 𝟘 = refl
+-zeroʳ 𝟙 = refl
+-zeroʳ 𝟚 = refl
+-zeroʳ ω = refl

-- The value ω is a zero for _+_.

+-zero : Zero ω _+_
-- +-zero = (λ _ → refl) , +-zeroʳ
+-zero = (λ{𝟘 → refl
          ; 𝟙 → refl
          ; 𝟚 → refl
          ; ω → refl}) , +-zeroʳ

------------------------------------------------------------------------
-- Multiplication

-- Multiplication.

infixr 45 _·_

_·_ : Zero-one-twice-many → Zero-one-twice-many → Zero-one-twice-many
𝟘 · _ = 𝟘
_ · 𝟘 = 𝟘
p · 𝟙 = p
𝟙 · q = q
_ · _ = ω

-- -- Multiplication is idempotent.

-- ·-idempotent : Idempotent _·_
-- ·-idempotent 𝟘 = refl
-- ·-idempotent 𝟙 = refl
-- ·-idempotent 𝟚 = refl
-- ·-idempotent ω = refl

-- Multiplication is commutative.

·-comm : Commutative _·_
·-comm = λ where
  𝟘 𝟘 → refl
  𝟘 𝟙 → refl
  𝟘 𝟚 → refl
  𝟘 ω → refl
  𝟙 𝟘 → refl
  𝟙 𝟙 → refl
  𝟙 𝟚 → refl
  𝟙 ω → refl
  𝟚 𝟘 → refl
  𝟚 𝟙 → refl
  𝟚 𝟚 → refl
  𝟚 ω → refl
  ω 𝟘 → refl
  ω 𝟙 → refl
  ω 𝟚 → refl
  ω ω → refl

-- If p is not 𝟘, then ω · p is equal to ω.

ω·≢𝟘 : p ≢ 𝟘 → ω · p ≡ ω
ω·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
ω·≢𝟘 {p = 𝟙} _   = refl
ω·≢𝟘 {p = 𝟚} _   = refl
ω·≢𝟘 {p = ω} _   = refl

opaque

  -- If p is not 𝟘, then p · ω is equal to ω.

  ≢𝟘·ω : p ≢ 𝟘 → p · ω ≡ ω
  ≢𝟘·ω {(𝟘)} 𝟘≢𝟘 = ⊥-elim (𝟘≢𝟘 refl)
  ≢𝟘·ω {(𝟙)} _ = refl
  ≢𝟘·ω {(𝟚)} _ = refl
  ≢𝟘·ω {(ω)} _ = refl

-- If p is not 𝟘, then 𝟙 · p is not 𝟘.

𝟙·≢𝟘 : p ≢ 𝟘 → 𝟙 · p ≢ 𝟘
𝟙·≢𝟘 {p = 𝟘} 𝟘≢𝟘 = 𝟘≢𝟘
𝟙·≢𝟘 {p = 𝟙} 𝟙≢𝟘 = 𝟙≢𝟘
𝟙·≢𝟘 {p = 𝟚} 𝟙≢𝟘 = 𝟙≢𝟘
𝟙·≢𝟘 {p = ω} ω≢𝟘 = ω≢𝟘

-- The value of ω · p is not 𝟙.

ω·≢𝟙 : ω · p ≢ 𝟙
ω·≢𝟙 {p = 𝟘} ()
ω·≢𝟙 {p = 𝟙} ()
ω·≢𝟙 {p = 𝟚} ()
ω·≢𝟙 {p = ω} ()

opaque

  -- The grade ω · (p + q) is bounded by ω · q.

  ω·+≤ω·ʳ : ∀ p → ω · (p + q) ≤ ω · q
  ω·+≤ω·ʳ {q = 𝟘} 𝟘 = refl
  ω·+≤ω·ʳ {q = 𝟙} 𝟘 = refl
  ω·+≤ω·ʳ {q = 𝟚} 𝟘 = refl
  ω·+≤ω·ʳ {q = ω} 𝟘 = refl
  ω·+≤ω·ʳ {q = 𝟘} 𝟙 = refl
  ω·+≤ω·ʳ {q = 𝟙} 𝟙 = refl
  ω·+≤ω·ʳ {q = 𝟚} 𝟙 = refl
  ω·+≤ω·ʳ {q = ω} 𝟙 = refl
  ω·+≤ω·ʳ {q = 𝟘} 𝟚 = refl
  ω·+≤ω·ʳ {q = 𝟙} 𝟚 = refl
  ω·+≤ω·ʳ {q = 𝟚} 𝟚 = refl
  ω·+≤ω·ʳ {q = ω} 𝟚 = refl
  ω·+≤ω·ʳ {q = 𝟘} ω = refl
  ω·+≤ω·ʳ {q = 𝟙} ω = refl
  ω·+≤ω·ʳ {q = 𝟚} ω = refl
  ω·+≤ω·ʳ {q = ω} ω = refl

------------------------------------------------------------------------
-- The modality without the star operation

-- The zero-one-twice-many semiring with meet

zero-one-twice-many-semiring-with-meet : Semiring-with-meet
zero-one-twice-many-semiring-with-meet = record
  { _+_          = _+_
  ; _·_          = _·_
  ; _∧_          = _∧_
  ; 𝟘            = 𝟘
  ; 𝟙            = 𝟙
  ; ω            = ω
  ; ω≤𝟙          = refl
  ; ω·+≤ω·ʳ      = λ {p = p} → ω·+≤ω·ʳ p
  ; is-𝟘?        = _≟ 𝟘
  ; +-·-Semiring = record
    { isSemiringWithoutAnnihilatingZero = record
      { +-isCommutativeMonoid = record
        { isMonoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = PE.isEquivalence
              ; ∙-cong = cong₂ _+_
              }
            ; assoc = λ where
                𝟘 _ _ → refl
                𝟙 𝟘 𝟘 → refl
                𝟙 𝟘 𝟙 → refl
                𝟙 𝟘 𝟚 → refl
                𝟙 𝟘 ω → refl
                𝟙 𝟙 𝟘 → refl
                𝟙 𝟙 𝟙 → refl
                𝟙 𝟙 ω → refl
                𝟙 ω 𝟘 → refl
                𝟙 ω 𝟙 → refl
                𝟙 ω 𝟚 → refl
                𝟙 ω ω → refl
                ω 𝟘 𝟘 → refl
                ω 𝟘 𝟙 → refl
                ω 𝟘 𝟚 → refl
                ω 𝟘 ω → refl
                ω 𝟙 𝟘 → refl
                ω 𝟙 𝟙 → refl
                ω 𝟙 ω → refl
                ω ω 𝟘 → refl
                ω ω 𝟙 → refl
                ω ω 𝟚 → refl
                ω ω ω → refl
                𝟙 𝟙 𝟚 → refl
                𝟙 𝟚 𝟘 → refl
                𝟙 𝟚 𝟙 → refl
                𝟙 𝟚 𝟚 → refl
                𝟙 𝟚 ω → refl
                𝟚 𝟘 𝟘 → refl
                𝟚 𝟘 𝟙 → refl
                𝟚 𝟘 𝟚 → refl
                𝟚 𝟘 ω → refl
                𝟚 𝟙 𝟘 → refl
                𝟚 𝟙 𝟙 → refl
                𝟚 𝟙 𝟚 → refl
                𝟚 𝟙 ω → refl
                𝟚 𝟚 𝟘 → refl
                𝟚 𝟚 𝟙 → refl
                𝟚 𝟚 𝟚 → refl
                𝟚 𝟚 ω → refl
                𝟚 ω 𝟘 → refl
                𝟚 ω 𝟙 → refl
                𝟚 ω 𝟚 → refl
                𝟚 ω ω → refl
                ω 𝟙 𝟚 → refl
                ω 𝟚 𝟘 → refl
                ω 𝟚 𝟙 → refl
                ω 𝟚 𝟚 → refl
                ω 𝟚 ω → refl
            }
          ; identity =
                (λ _ → refl)
              , comm∧idˡ⇒idʳ +-comm (λ _ → refl)
          }
        ; comm = +-comm
        }
        ; *-cong = cong₂ _·_
        ; *-assoc = λ where
              𝟘 _ _ → refl
              𝟙 𝟘 _ → refl
              𝟙 𝟙 𝟘 → refl
              𝟙 𝟙 𝟙 → refl
              𝟙 𝟙 𝟚 → refl
              𝟙 𝟙 ω → refl
              𝟙 𝟚 𝟘 → refl
              𝟙 𝟚 𝟙 → refl
              𝟙 𝟚 𝟚 → refl
              𝟙 𝟚 ω → refl
              𝟙 ω 𝟘 → refl
              𝟙 ω 𝟙 → refl
              𝟙 ω 𝟚 → refl
              𝟙 ω ω → refl
              𝟚 𝟘 _ → refl
              𝟚 𝟙 𝟘 → refl
              𝟚 𝟙 𝟙 → refl
              𝟚 𝟙 𝟚 → refl
              𝟚 𝟙 ω → refl
              𝟚 𝟚 𝟘 → refl
              𝟚 𝟚 𝟙 → refl
              𝟚 𝟚 𝟚 → refl
              𝟚 𝟚 ω → refl
              𝟚 ω 𝟘 → refl
              𝟚 ω 𝟙 → refl
              𝟚 ω 𝟚 → refl
              𝟚 ω ω → refl
              ω 𝟘 _ → refl
              ω 𝟙 𝟘 → refl
              ω 𝟙 𝟙 → refl
              ω 𝟙 𝟚 → refl
              ω 𝟙 ω → refl
              ω 𝟚 𝟘 → refl
              ω 𝟚 𝟙 → refl
              ω 𝟚 𝟚 → refl
              ω 𝟚 ω → refl
              ω ω 𝟘 → refl
              ω ω 𝟙 → refl
              ω ω 𝟚 → refl
              ω ω ω → refl
        ; *-identity =
                ·-identityˡ
              , comm∧idˡ⇒idʳ ·-comm ·-identityˡ
      ; distrib =
            ·-distrib-+ˡ
          , comm∧distrˡ⇒distrʳ ·-comm ·-distrib-+ˡ
      }
    ; zero =
          (λ _ → refl)
        , comm∧zeˡ⇒zeʳ ·-comm (λ _ → refl)
    }
  ; ∧-Semilattice = record
    { isBand = record
      { isSemigroup = record
        { isMagma = record
          { isEquivalence = PE.isEquivalence
          ; ∙-cong        = cong₂ _∧_
          }
        ; assoc = λ where
            𝟘 𝟘 𝟘 → refl
            𝟘 𝟘 𝟙 → refl
            𝟘 𝟘 𝟚 → refl
            𝟘 𝟘 ω → refl
            𝟘 𝟙 𝟘 → refl
            𝟘 𝟙 𝟙 → refl
            𝟘 𝟙 𝟚 → refl
            𝟘 𝟙 ω → refl
            𝟘 𝟚 𝟘 → refl
            𝟘 𝟚 𝟙 → refl
            𝟘 𝟚 𝟚 → refl
            𝟘 𝟚 ω → refl
            𝟘 ω c → refl
            𝟙 𝟘 𝟘 → refl
            𝟙 𝟘 𝟙 → refl
            𝟙 𝟘 𝟚 → refl
            𝟙 𝟘 ω → refl
            𝟙 𝟙 𝟘 → refl
            𝟙 𝟙 𝟙 → refl
            𝟙 𝟙 ω → refl
            𝟙 ω 𝟘 → refl
            𝟙 ω 𝟙 → refl
            𝟙 ω 𝟚 → refl
            𝟙 ω ω → refl
            ω 𝟘 𝟘 → refl
            ω 𝟘 𝟙 → refl
            ω 𝟘 𝟚 → refl
            ω 𝟘 ω → refl
            ω 𝟙 𝟘 → refl
            ω 𝟙 𝟙 → refl
            ω 𝟙 ω → refl
            ω ω 𝟘 → refl
            ω ω 𝟙 → refl
            ω ω 𝟚 → refl
            ω ω ω → refl
            𝟙 𝟙 𝟚 → refl
            𝟙 𝟚 𝟘 → refl
            𝟙 𝟚 𝟙 → refl
            𝟙 𝟚 𝟚 → refl
            𝟙 𝟚 ω → refl
            𝟚 𝟘 𝟘 → refl
            𝟚 𝟘 𝟙 → refl
            𝟚 𝟘 𝟚 → refl
            𝟚 𝟘 ω → refl
            𝟚 𝟙 𝟘 → refl
            𝟚 𝟙 𝟙 → refl
            𝟚 𝟙 𝟚 → refl
            𝟚 𝟙 ω → refl
            𝟚 𝟚 𝟘 → refl
            𝟚 𝟚 𝟙 → refl
            𝟚 𝟚 𝟚 → refl
            𝟚 𝟚 ω → refl
            𝟚 ω 𝟘 → refl
            𝟚 ω 𝟙 → refl
            𝟚 ω 𝟚 → refl
            𝟚 ω ω → refl
            ω 𝟙 𝟚 → refl
            ω 𝟚 𝟘 → refl
            ω 𝟚 𝟙 → refl
            ω 𝟚 𝟚 → refl
            ω 𝟚 ω → refl
        }
      ; idem = λ where
          𝟘 → refl
          𝟙 → refl
          𝟚 → refl
          ω → refl
      }
    ; comm = ∧-comm
    }
  ; ·-distrib-∧ =
        ·-distrib-∧ˡ
      , comm∧distrˡ⇒distrʳ ·-comm ·-distrib-∧ˡ
  ; +-distrib-∧ =
        +-distrib-∧ˡ
      , comm∧distrˡ⇒distrʳ +-comm +-distrib-∧ˡ
  }
  where
  open Tools.Reasoning.PropositionalEquality

  +-comm : Commutative _+_
  +-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 𝟚 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 𝟚 → refl
    𝟙 ω → refl
    𝟚 𝟘 → refl
    𝟚 𝟙 → refl
    𝟚 𝟚 → refl
    𝟚 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω 𝟚 → refl
    ω ω → refl

  ·-identityˡ : LeftIdentity 𝟙 _·_
  ·-identityˡ = λ where
    𝟘 → refl
    𝟙 → refl
    𝟚 → refl
    ω → refl

  ·-distrib-+ˡ : _·_ DistributesOverˡ _+_
  ·-distrib-+ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 _ → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 → refl
    𝟙 ω 𝟚 → refl
    𝟙 ω ω → refl
    ω 𝟘 _ → refl
    ω 𝟙 𝟘 → refl
    ω 𝟙 𝟙 → refl
    ω 𝟙 ω → refl
    ω ω 𝟘 → refl
    ω ω 𝟙 → refl
    ω ω 𝟚 → refl
    ω ω ω → refl
    𝟙 𝟙 𝟚 → refl
    𝟙 𝟚 𝟘 → refl
    𝟙 𝟚 𝟙 → refl
    𝟙 𝟚 𝟚 → refl
    𝟙 𝟚 ω → refl
    𝟚 𝟘 c → refl
    𝟚 𝟙 𝟘 → refl
    𝟚 𝟙 𝟙 → refl
    𝟚 𝟙 𝟚 → refl
    𝟚 𝟙 ω → refl
    𝟚 𝟚 𝟘 → refl
    𝟚 𝟚 𝟙 → refl
    𝟚 𝟚 𝟚 → refl
    𝟚 𝟚 ω → refl
    𝟚 ω 𝟘 → refl
    𝟚 ω 𝟙 → refl
    𝟚 ω 𝟚 → refl
    𝟚 ω ω → refl
    ω 𝟙 𝟚 → refl
    ω 𝟚 𝟘 → refl
    ω 𝟚 𝟙 → refl
    ω 𝟚 𝟚 → refl
    ω 𝟚 ω → refl

  ∧-comm : Commutative _∧_
  ∧-comm = λ where
    𝟘 𝟘 → refl
    𝟘 𝟙 → refl
    𝟘 𝟚 → refl
    𝟘 ω → refl
    𝟙 𝟘 → refl
    𝟙 𝟙 → refl
    𝟙 𝟚 → refl
    𝟙 ω → refl
    𝟚 𝟘 → refl
    𝟚 𝟙 → refl
    𝟚 𝟚 → refl
    𝟚 ω → refl
    ω 𝟘 → refl
    ω 𝟙 → refl
    ω 𝟚 → refl
    ω ω → refl

  ·-distrib-∧ˡ : _·_ DistributesOverˡ _∧_
  ·-distrib-∧ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟚 → refl
    𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 → refl
    𝟙 ω 𝟚 → refl
    𝟙 ω ω → refl
    ω 𝟘 𝟘 → refl
    ω 𝟘 𝟙 → refl
    ω 𝟘 𝟚 → refl
    ω 𝟘 ω → refl
    ω 𝟙 𝟘 → refl
    ω 𝟙 𝟙 → refl
    ω 𝟙 ω → refl
    ω ω 𝟘 → refl
    ω ω 𝟙 → refl
    ω ω 𝟚 → refl
    ω ω ω → refl
    𝟙 𝟙 𝟚 → refl
    𝟙 𝟚 𝟘 → refl
    𝟙 𝟚 𝟙 → refl
    𝟙 𝟚 𝟚 → refl
    𝟙 𝟚 ω → refl
    𝟚 𝟘 𝟘 → refl
    𝟚 𝟘 𝟙 → refl
    𝟚 𝟘 𝟚 → refl
    𝟚 𝟘 ω → refl
    𝟚 𝟙 𝟘 → refl
    𝟚 𝟙 𝟙 → refl
    𝟚 𝟙 𝟚 → refl
    𝟚 𝟙 ω → refl
    𝟚 𝟚 𝟘 → refl
    𝟚 𝟚 𝟙 → refl
    𝟚 𝟚 𝟚 → refl
    𝟚 𝟚 ω → refl
    𝟚 ω 𝟘 → refl
    𝟚 ω 𝟙 → refl
    𝟚 ω 𝟚 → refl
    𝟚 ω ω → refl
    ω 𝟙 𝟚 → refl
    ω 𝟚 𝟘 → refl
    ω 𝟚 𝟙 → refl
    ω 𝟚 𝟚 → refl
    ω 𝟚 ω → refl


  +-distrib-∧ˡ : _+_ DistributesOverˡ _∧_
  +-distrib-∧ˡ = λ where
    𝟘 _ _ → refl
    𝟙 𝟘 𝟘 → refl
    𝟙 𝟘 𝟙 → refl
    𝟙 𝟘 𝟚 → refl
    𝟙 𝟘 ω → refl
    𝟙 𝟙 𝟘 → refl
    𝟙 𝟙 𝟙 → refl
    𝟙 𝟙 ω → refl
    𝟙 ω 𝟘 → refl
    𝟙 ω 𝟙 → refl
    𝟙 ω 𝟚 → refl
    𝟙 ω ω → refl
    ω 𝟘 𝟘 → refl
    ω 𝟘 𝟙 → refl
    ω 𝟘 𝟚 → refl
    ω 𝟘 ω → refl
    ω 𝟙 𝟘 → refl
    ω 𝟙 𝟙 → refl
    ω 𝟙 ω → refl
    ω ω 𝟘 → refl
    ω ω 𝟙 → refl
    ω ω 𝟚 → refl
    ω ω ω → refl
    𝟙 𝟙 𝟚 → refl
    𝟙 𝟚 𝟘 → refl
    𝟙 𝟚 𝟙 → refl
    𝟙 𝟚 𝟚 → refl
    𝟙 𝟚 ω → refl
    𝟚 𝟘 𝟘 → refl
    𝟚 𝟘 𝟙 → refl
    𝟚 𝟘 𝟚 → refl
    𝟚 𝟘 ω → refl
    𝟚 𝟙 𝟘 → refl
    𝟚 𝟙 𝟙 → refl
    𝟚 𝟙 𝟚 → refl
    𝟚 𝟙 ω → refl
    𝟚 𝟚 𝟘 → refl
    𝟚 𝟚 𝟙 → refl
    𝟚 𝟚 𝟚 → refl
    𝟚 𝟚 ω → refl
    𝟚 ω 𝟘 → refl
    𝟚 ω 𝟙 → refl
    𝟚 ω 𝟚 → refl
    𝟚 ω ω → refl
    ω 𝟙 𝟚 → refl
    ω 𝟚 𝟘 → refl
    ω 𝟚 𝟙 → refl
    ω 𝟚 𝟚 → refl
    ω 𝟚 ω → refl


instance

  zero-one-twice-many-has-well-behaved-zero :
    Has-well-behaved-zero zero-one-twice-many-semiring-with-meet
  zero-one-twice-many-has-well-behaved-zero = record
    { non-trivial = λ ()
    ; zero-product =  λ where
        {p = 𝟘}         _  → inj₁ refl
        {q = 𝟘}         _  → inj₂ refl
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = ω} ()
        {p = ω} {q = 𝟙} ()
        {p = ω} {q = ω} ()
    ; +-positiveˡ =  λ where
        {p = 𝟘} {q = 𝟘} _  → refl
        {p = 𝟘} {q = 𝟙} ()
        {p = 𝟘} {q = 𝟚} ()
        {p = 𝟘} {q = ω} ()
        {p = 𝟙} {q = 𝟘} ()
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = 𝟚} ()
        {p = 𝟙} {q = ω} ()
        {p = 𝟚} {q = 𝟘} ()
        {p = 𝟚} {q = 𝟙} ()
        {p = 𝟚} {q = 𝟚} ()
        {p = 𝟚} {q = ω} ()
        {p = ω} {q = 𝟘} ()
        {p = ω} {q = 𝟙} ()
        {p = ω} {q = 𝟚} ()
        {p = ω} {q = ω} ()
    ; ∧-positiveˡ = λ where
        {p = 𝟘} {q = 𝟘} _     → refl
        {p = 𝟘} {q = 𝟙} _     → refl
        {p = 𝟙} {q = 𝟘} 𝟙≡𝟘 →
          ⊥-elim (
            case
              𝟙  ≡⟨ 𝟘-maximal (sym 𝟙≡𝟘) ⟩
              𝟘  ∎
            of λ ())
        {p = 𝟘} {q = ω} ()
        {p = 𝟙} {q = 𝟙} ()
        {p = 𝟙} {q = ω} ()
        {p = ω}         ()
    }
    where open Tools.Reasoning.PropositionalEquality

zero-one-twice-many-modality : Modality
zero-one-twice-many-modality = record
  { variant            = record { 𝟘ᵐ-allowed = true }
  ; semiring-with-meet = zero-one-twice-many-semiring-with-meet
  ; 𝟘-well-behaved     = λ _ → zero-one-twice-many-has-well-behaved-zero
  }
