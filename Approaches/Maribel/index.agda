open import Data.Nat using (ℕ; suc)
open import Data.Fin
open import Data.Fin.Properties hiding (all?)
open import Data.Vec hiding ([_])
open import Data.Product
open import Data.Empty
open import Data.Maybe
open import Agda.Builtin.Unit
open import Data.Vec.Relation.Unary.All using (All; all?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable
open import Agda.Builtin.Sigma
open import Function.Base
open import Agda.Primitive

data Use : Set where
  #2 #1 #0 : Use
-- Use : Set
-- Use = Fin 3

data Use-Pred : Use → Use → Set where
  2↓ : Use-Pred #2 #1
  1↓ : Use-Pred #1 #0

Names : Set
Names = ℕ

M : Names → Set
M = Vec Use

CtxTy : Names → Set₁
CtxTy Γ = M Γ → M Γ → Set

CtxTy′ : ∀ {ℓ} Names → Set (lsuc ℓ)
CtxTy′ {ℓ} Γ = M Γ → M Γ → Set ℓ

-- Variable of type t
data Var : {Γ : Names} → CtxTy Γ where
  -- consumes multiplicity
  here : ∀ {Γ h h′ m}
    → Use-Pred h h′
    → Var {suc Γ} (h ∷ m) (h′ ∷ m)
  -- somewhere else in the context
  there : ∀ {Γ h m n}
    → Var {Γ} m n
    → Var {suc Γ} (h ∷ m) (h ∷ n)

pattern here₂ = here 2↓
pattern here₁ = here 1↓

-- v#: {Γ : Names} → {m : M Γ} → (idx : Fin Γ) → {_ : False (lookup m idx ≟ zero)} → Σ (M Γ) (λ n → Var m n)
-- v#{Γ} {[]} ()
-- v#{Γ} {suc zero ∷ m} zero = #0 ∷ m , here₁
-- v#{Γ} {suc (suc zero) ∷ m} zero = #1 ∷ m , here₂
-- v#{Γ} {zero ∷ m} zero {()}
-- v#{Γ} {h ∷ m} (suc idx) {x} =
--   let m' , v' = v#{m = m} idx {x}
--   in h ∷ m' , (there v')

record Alphabet : Set₁ where
  field
    Agent : Set
    arity : Agent → ℕ
open Alphabet

data Term {{σ : Alphabet}} : {Γ : Names} → CtxTy Γ

data Vars {{σ : Alphabet}} {Γ : Names} : (len : ℕ) → CtxTy Γ where
  [] : ∀ {m} → Vars 0 m m
  _∷_ : ∀ {m n o len}
    → Term m n
    → Vars len n o
    → Vars (suc len) m o
infixr 5 _∷_

-- inet
data Term {{σ}} where
  name : ∀ {Γ : Names} {m n : M Γ}
    → Var m n
    → Term m n
  _⟨_⟩ : ∀ (ag : Agent σ)
    → {Γ : Names} {m n : M Γ}
    → (vars : Vars {{σ}} (arity σ ag) m n)
    → Term m n
infixl 8 _⟨_⟩

pattern _⟨⟩ ag = ag ⟨ [] ⟩

Alphabet-example : Alphabet
Alphabet-example = record
  { Agent = ⊤
  ; arity = λ{tt → 2}
  }

example₁ : Term {{Alphabet-example}} (#2 ∷ []) (#0 ∷ [])
example₁ = tt ⟨ name here₂ ∷ name here₁ ∷ [] ⟩

example₂ : Term {{Alphabet-example}} (#1 ∷ #1 ∷ []) (#0 ∷ #0 ∷ [])
example₂ = tt ⟨ name here₁ ∷ name (there here₁) ∷ [] ⟩

data IntCombAgent : Set where
  ε δ γ : IntCombAgent

Alphabet-comb : Alphabet
Alphabet-comb = record
  { Agent = IntCombAgent
  ; arity = λ{ε → 0; δ → 2; γ → 2}
  }

-- example₃ : Term {{Alphabet-comb}} (#1 ∷ #1 ∷ []) (#0 ∷ #0 ∷ [])
-- example₃ = δ ⟨ name (snd (v##0)) ∷ name (snd (v##1)) ∷ [] ⟩

Equation : ∀ {{σ : Alphabet}} {Γ : Names} {m n o : M Γ} → (α : Term m n) → (β : Term n o) → Term m n × Term n o
Equation α β = α , β

record Rule {{σ : Alphabet}} : Set where
  field
    α β : Agent σ
    Γ : Names
    a b c : M Γ

    {{a-ok}} : All (λ x → x ≡ #2) a
    {{c-ok}} : All (λ x → x ≡ #0) c
    -- {{c-ok}} : From-yes (all? (λ x → x ≟ #0) c)

    α-vars : Vars (arity σ α) a b
    β-vars : Vars (arity σ β) b c

data NatAgent : Set where
  Z S Add : NatAgent

Nat-alphabet : Alphabet
Nat-alphabet = record
  { Agent = NatAgent
  ; arity = λ{Z → 0; S → 1; Add → 2}
  }

Nat-rule₁ : Rule {{Nat-alphabet}}
Nat-rule₁ = record
  { α = Add
  ; β = S
  ; Γ = 2
  ; a = #2 ∷ #2 ∷ []
  ; b = #1 ∷ #1 ∷ []
  ; c = #0 ∷ #0 ∷ []
  ; a-ok = refl All.∷ (refl All.∷  All.[] )
  ; c-ok = refl All.∷ (refl All.∷  All.[] )
  ; α-vars = S ⟨ name here₂ ∷ [] ⟩ ∷ (name (there here₂)) ∷ []
  ; β-vars = (Add ⟨ name here₁ ∷ (name (there here₁) ∷ []) ⟩) ∷ []
  }

Nat-rule₂ : Rule {{Nat-alphabet}}
Nat-rule₂ = record
  { α = Add
  ; β = Z
  ; Γ = 1
  ; a = #2 ∷ []
  ; b = #0 ∷ []
  ; c = #0 ∷ []
  ; a-ok = refl All.∷  All.[]
  ; c-ok = refl All.∷  All.[]
  ; α-vars = name here₂ ∷ name here₁ ∷ []
  ; β-vars = []
  }

Nat-rules : (NatAgent × NatAgent) → Maybe (Rule {{Nat-alphabet}})
Nat-rules (Add , S) = just Nat-rule₁
Nat-rules (Add , Z) = just Nat-rule₂
Nat-rules _ = nothing

record Configuration {{σ : Alphabet}} {Γ : Names} : Set where
  field
    -- t : multiset/sequentiated-indexed list of terms(Vars, CombinedTerm)
    -- for now a single term
    m {n o k} : M Γ
    t : Maybe (Term m n)
    R : (Agent σ × Agent σ) → Maybe Rule
    -- Δ : List Equation
    -- for now a single equation
    Δ : Maybe (Term n o × Term o k)

1+0-config : Configuration {{Nat-alphabet}} {1}
1+0-config = record
  { t = just (name here₂)
  ; R = Nat-rules
  ; Δ = just (Add ⟨ name here₁ ∷ Z ⟨⟩ ∷ [] ⟩ , S ⟨ Z ⟨⟩ ∷ [] ⟩)
  ; m = #2 ∷ []
  }

open import Data.List using (List; []; _∷_)
-- strings together a list of types that require in/out uses list
data Scope {ℓ} {{σ : Alphabet}} {Γ : Names} : List (CtxTy′ {ℓ} Γ) → CtxTy′ {lsuc ℓ} Γ where
  [] : ∀ {m} → Scope [] m m
  _∷_ : {A : CtxTy′ Γ} {tys : List (CtxTy′ Γ)} {m n o : M Γ}
    → A m n
    → (ctx : Scope tys n o)
    → Scope (A ∷ tys) m o

Rule′ : {{σ : Alphabet}} → {Names} → (α β : Agent σ) → Set₁
Rule′ {{σ}} {Γ} α β = Scope
  (Vars (arity σ α) ∷ Vars (arity σ β) ∷ [])
  (replicate Γ #2)
  (replicate Γ #0)

Nat-rule₁′ : Rule′ {{Nat-alphabet}} {2} Add S
Nat-rule₁′ =
  ( (S ⟨ (name here₂) ∷ [] ⟩ ∷ name (there here₂) ∷ [])
  ∷ (Add ⟨ name here₁ ∷ name (there here₁) ∷ [] ⟩ ∷ [])
  ∷ [])

-- Interaction Net System
record INS : Set₁ where
  field
    {{σ}} : Alphabet
    R : (α β : Agent σ) → Maybe (Σ Names (λ Γ → Rule′ {Γ} α β))

Nat-INS : INS
Nat-INS = record
  { σ = Nat-alphabet
  ; R = λ{Add S → just (2 , Nat-rule₁′)
        ; _ _ → nothing}
  }

record Configuration′ {{σ : Alphabet}} {Γ : Names} : Set₁ where
  field
    {m n} : M Γ
    t : Scope
      ( Term -- initial term
        ∷ Term -- lhs of delta
        ∷ Term -- rhs of delta
        ∷ []
        -- lhs+rhs of delta was (λ m n → Σ (M Γ) (λ k → (Term m k × Term k n)))
      )
      m n
    R : ∀ (α β : Agent σ) → Maybe (Σ Names (λ Γ → Rule′ {Γ} α β))

1+0-config′ : Configuration′ {{Nat-alphabet}} {1}
1+0-config′ = record
  { t = name here₂ ∷ (Add ⟨ name here₁ ∷ Z ⟨⟩ ∷ [] ⟩) ∷ S ⟨ Z ⟨⟩ ∷ [] ⟩ ∷ []
  ; m = #2 ∷ []
  ; R = λ{Add S → just (2 , Nat-rule₁′)
        ; _ _ → nothing} }

-- connected tuple of terms
record Equation′ {{σ : Alphabet}} {Γ : Names} (m n : M Γ) : Set where
  constructor _＝_
  field
    {k} : M Γ
    lhs : Term m k
    rhs : Term k n
infix 4 _＝_

-- eq₁ : Equation′ {{Nat-alphabet}} {2} {!   !} {!   !}
-- eq₁ = Z ⟨⟩ ＝ Z ⟨⟩

import Data.List as List
record Configuration″ {{σ : Alphabet}} {Γ : Names} : Set₂ where
  field
    {m n} : M Γ
    {t-len Δ-len} : ℕ
    t :
      Scope
        ( Scope (List.replicate t-len Term)
        ∷ Scope (List.replicate Δ-len Equation′)
        ∷ [])
        m n
    R : ∀ (α β : Agent σ) → Maybe (Σ Names (λ Γ → Rule′ {Γ} α β))

1+0-config″ : Configuration″ {{Nat-alphabet}} {1}
1+0-config″ = record
  { t = 
    ( (name here₂ ∷ [])
    ∷ ((Add ⟨ name here₁ ∷ Z ⟨⟩ ∷ [] ⟩ ＝ S ⟨ Z ⟨⟩ ∷ [] ⟩) ∷ [])
    ∷ [])
  ; m = #2 ∷ []
  ; R = λ{Add S → just (2 , Nat-rule₁′)
        ; _ _ → nothing} } 

open import Data.Product
Configuration‴ : {{ins : INS}} {Γ : Names} → {t-len Δ-len : ℕ} → Set₂
Configuration‴ {{ins}} {Γ} {t-len} {Δ-len} =
  ∃₂ (Scope {Γ = Γ}
        ( Scope (List.replicate t-len Term)
        ∷ Scope (List.replicate Δ-len Equation′)
        ∷ [])
      )

1+0-config‴ : Configuration‴ {{Nat-INS}} {1} {1} {1}
1+0-config‴ = #2 ∷ [] , _ , 
  ( (name here₂ ∷ [])
    ∷ ((Add ⟨ name here₁ ∷ Z ⟨⟩ ∷ [] ⟩ ＝ S ⟨ Z ⟨⟩ ∷ [] ⟩) ∷ [])
    ∷ [])

record Configuration⁗ {{σ : Alphabet}} : Set₂ where
  constructor ⟨_,⟨_∣_⟩⟩
  field
    {Γ} : Names
    {m n o} : M Γ
    {t-len Δ-len} : ℕ
    R : ∀ (α β : Agent σ) → Maybe (Σ Names (λ Γ → Rule′ {Γ} α β))
    t : Scope (List.replicate t-len Term) m n
    Δ : Scope (List.replicate Δ-len Equation′) n o

1+0-config⁗ : Configuration⁗ {{Nat-alphabet}}
1+0-config⁗ = record
  { m = #2 ∷ []
  ; R = INS.R Nat-INS
  ; t = name here₂ ∷ []
  ; Δ = (Add ⟨ name here₁ ∷ Z ⟨⟩ ∷ [] ⟩ ＝ S ⟨ Z ⟨⟩ ∷ [] ⟩) ∷ []
  }

-- empty-cfg : Configuration⁗ {{Nat-alphabet}}
-- empty-cfg = ⟨ (λ _ _ → nothing) ,⟨ [] ∣ [] ⟩⟩

