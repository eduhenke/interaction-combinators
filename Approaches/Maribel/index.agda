open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties
open import Data.Vec hiding ([_]; lookup)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; uncurry′; ∃; _,_)
open import Data.Product using () renaming (_×_ to _×′_)
open import Data.Empty
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Unit
open import Data.Vec.Relation.Unary.All using (All; all?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans)
open import Relation.Nullary.Decidable
open import Agda.Builtin.Sigma
open import Function.Base
open import Agda.Primitive
import Data.Vec.Membership.Propositional as Member
open Member using (_∈_)
import Data.Vec.Relation.Unary.Any as Any
open Any using (Any; here; there)

data Use : Set where
  #2 #1 #0 : Use

data Use-Pred : (Use ×′ Use) → Set where
  2↓ : Use-Pred (#2 , #1)
  1↓ : Use-Pred (#1 , #0)

Names : Set
Names = ℕ

-- Multiplicities
M : Names → Set
M = Vec Use

CtxTy : Names → Set₁
CtxTy Γ = M Γ → M Γ → Set

record Alphabet : Set₁ where
  field
    AgentTy : Set
    arity : AgentTy → ℕ
open Alphabet

record _×_ {{σ : Alphabet}} {Γ : Names} (A B : CtxTy Γ) (m n : M Γ) : Set where
  constructor _,_
  field
    {k} : M Γ
    lhs : A m k
    rhs : B k n

-- strings together a list of a type that require in/out multiplicities
data Scope {{σ : Alphabet}} {Γ : Names} (A : CtxTy Γ) : ℕ → CtxTy Γ where
  [] : ∀ {m} → Scope A 0 m m
  _∷_ : {m k n : M Γ} {l : ℕ}
    → A m k
    → (ctx : Scope A l k n)
    → Scope A (suc l) m n

Var : ∀ {Γ : Names} → CtxTy Γ
Var m n = Any Use-Pred (zip m n)

-- sublist
infix 3 _⊆_

data _⊆_ {A : Set} : ∀ {n n′ : ℕ} → Vec A n → Vec A n′ → Set  where
  base : [] ⊆ []
  skip : ∀ {n n′ : ℕ} {y : A} {xs : Vec A n} {ys : Vec A n′}
    → xs ⊆ ys → xs ⊆ (y ∷ ys)
  keep : ∀ {n n′ : ℕ} {x : A} {xs : Vec A n} {ys : Vec A n′}
    → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

lookup : ∀ {A} {n n′ : ℕ} {xs : Vec A n} {ys : Vec A n′}
  → xs ⊆ ys → {x : A} → x ∈ xs → x ∈ ys
lookup (skip p) v         = there (lookup p v)
lookup (keep p) (here px) = here px
lookup (keep p) (there v) = there (lookup p v)
lookup base     ()
---

var→∈ : ∀ {Γ} {m n : M Γ} {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}}
  → Var m n
  → ∃[ x ] x ∈ mn ×′ Use-Pred x
var→∈ {{refl}} = Member.find

∈→var : ∀ {Γ} {m n : M Γ} {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}} {v}
  → v ∈ mn
  → Use-Pred v
  → Var m n
∈→var {{refl}} v-in p = Any.map (λ{refl → p}) v-in

weaken : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}}
  {mn′ : Vec (Use ×′ Use) Γ′} {{mn′≡ : mn′ ≡ zip m′ n′}}
  → mn ⊆ mn′
  → Var m n
  → Var m′ n′
weaken mn⊆mn′ v =
  let _ , x-in , Ux = var→∈ v
  in ∈→var (lookup mn⊆mn′ x-in) Ux

pattern here₂ = here 2↓
pattern here₁ = here 1↓

data Term {{σ : Alphabet}} : {Γ : Names} → CtxTy Γ

Vars : ∀ {{σ : Alphabet}} {Γ : Names} → ℕ → CtxTy Γ
Vars = Scope Term

record Agent {{σ : Alphabet}} {Γ : Names} (α : AgentTy σ) (m n : M Γ) : Set where
  inductive
  constructor _⟨_⟩
  field
    α′ : AgentTy σ
    {{α′-ok}} : α′ ≡ α
    args : Vars {{σ}} (arity σ α) m n

infixl 8 _⟨_⟩
pattern _⟨⟩ ag = ag ⟨ [] ⟩

-- inet
data Term {{σ}} where
  var : ∀ {Γ : Names} {m n : M Γ}
    → Var m n
    → Term m n
  agent_ : ∀ {Γ} {m n : M Γ} {α : AgentTy σ}
    → Agent α m n
    → Term m n
infixl 7 agent_

Rule : {{σ : Alphabet}} → {Γ : Names} → (α β : AgentTy σ) → Set
Rule {{σ}} {Γ} α β = (Agent α × Agent β) (replicate Γ #2) (replicate Γ #0)

Equation : {{σ : Alphabet}} {Γ : Names} → CtxTy Γ
Equation = Term × Term

pattern _＝_ a b = a , b
infix 4 _＝_

Alphabet-example : Alphabet
Alphabet-example = record
  { AgentTy = ⊤
  ; arity = λ{tt → 2}
  }

instance
  zeroUse : M 0
  zeroUse = []

example₁ : Term {{Alphabet-example}} (#2 ∷ []) (#0 ∷ [])
example₁ = agent tt ⟨ var (here 2↓) ∷ var (here {xs = []} 1↓) ∷ [] ⟩

example₂ : Term {{Alphabet-example}} (#1 ∷ #1 ∷ []) (#0 ∷ #0 ∷ [])
example₂ = agent tt ⟨ var here₁ ∷ var (there (here {xs = []} 1↓)) ∷ [] ⟩

data IntCombAgent : Set where
  ε δ γ : IntCombAgent

Alphabet-comb : Alphabet
Alphabet-comb = record
  { AgentTy = IntCombAgent
  ; arity = λ{ε → 0; δ → 2; γ → 2}
  }

data NatAgent : Set where
  Z S Add : NatAgent

Nat-alphabet : Alphabet
Nat-alphabet = record
  { AgentTy = NatAgent
  ; arity = λ{Z → 0; S → 1; Add → 2}
  }

Rules : ∀ {{σ : Alphabet}} → Set
Rules {{σ}} = ∀ (α β : AgentTy σ) → Maybe (∃[ Γ ] Rule {Γ} α β)

Nat-rules : Rules {{Nat-alphabet}}
Nat-rules Add S = just (2
    , Add ⟨ agent (S ⟨ var here₂ ∷ [] ⟩) ∷ var (there (here {xs = []} 2↓)) ∷ [] ⟩
    , S ⟨ agent (Add ⟨ var here₁ ∷ var (there (here {xs = []} 1↓)) ∷ [] ⟩) ∷ [] ⟩
  )
Nat-rules _ _ = nothing

record Configuration {{σ : Alphabet}} : Set₂ where
  constructor ⟨_,⟨_∣_⟩⟩
  field
    {Γ} : Names
    {m n o} : M Γ
    {t-len Δ-len} : ℕ
    R : ∀ (α β : AgentTy σ) → Maybe (Σ Names (λ Γ → Rule {Γ} α β))
    t : Scope Term t-len m n
    Δ : Scope Equation Δ-len n o

1+0-config : Configuration {{Nat-alphabet}}
1+0-config = record
  { m = #2 ∷ []
  ; R = Nat-rules
  ; t = var (here {xs = []} 2↓) ∷ []
  ; Δ = (agent Add ⟨ var (here {xs = []} 1↓) ∷ agent Z ⟨⟩ ∷ [] ⟩ ＝ agent S ⟨ agent Z ⟨⟩ ∷ [] ⟩) ∷ []
  }


infix 4 []⊆_
[]⊆_ : ∀ xs → [] ⊆ xs
[]⊆ []     = base
[]⊆ x ∷ xs = skip ([]⊆ xs)


mutual
  weaken-vars : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
    {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}}
    {mn′ : Vec (Use ×′ Use) Γ′} {{mn′≡ : mn′ ≡ zip m′ n′}}
    {l} {{σ : Alphabet}}
    → mn ⊆ mn′
    → Vars l m n
    → Vars l m′ n′
  weaken-term : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
    {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}}
    {mn′ : Vec (Use ×′ Use) Γ′} {{mn′≡ : mn′ ≡ zip m′ n′}}
    {{σ : Alphabet}}
    → mn ⊆ mn′
    → Term m n
    → Term m′ n′

  -- weaken-vars {m′ = []} {n′ = []} {{refl}} {{refl}} mn⊆mn′ v = {! v  !}
  -- weaken-vars {m = []} {n = []} {m′ = x′ ∷ m′} {n′ = y′ ∷ n′} ⦃ mn≡ = refl ⦄ ⦃ mn′≡ = refl ⦄ (skip mn⊆mn′) [] = {!   !}
  -- weaken-vars {m = []} {n = []} {m′ = x′ ∷ m′} {n′ = y′ ∷ n′} ⦃ mn≡ = refl ⦄ ⦃ mn′≡ = refl ⦄ (skip mn⊆mn′) (x ∷ v) = {!   !} ∷ (weaken-vars {! []⊆ ?  !} v)
  -- weaken-vars {m = x ∷ m} {n = y ∷ n} {m′ = x′ ∷ m′} {n′ = y′ ∷ n′} ⦃ mn≡ = refl ⦄ ⦃ mn′≡ = refl ⦄ (skip mn⊆mn′) v = {!   !}
  -- weaken-vars {m = x ∷ m} {n = y ∷ n} {m′ = x′ ∷ m′} {n′ = y′ ∷ n′} ⦃ mn≡ = refl ⦄ ⦃ mn′≡ = refl ⦄ (keep mn⊆mn′) v = {!   !}
  weaken-vars = {!   !}
  
  weaken-term {{refl}} {{refl}} mn⊆mn′ (var v) = var (weaken mn⊆mn′ v)
  weaken-term {{refl}} {{refl}} mn⊆mn′ (agent α ⟨ vs ⟩) = agent α ⟨ weaken-vars mn⊆mn′ vs ⟩

open import Data.Fin using (Fin)
open import Data.Vec.Properties


x⊆x : ∀ {n A} (x : Vec A n) → x ⊆ x
x⊆x [] = base
x⊆x (_ ∷ x) = keep (x⊆x x)

xs⊆ys++xs : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  → zip m′ n′ ⊆ zip (m ++ m′) (n ++ n′)
xs⊆ys++xs {m = []} {n = []} = x⊆x (zip _ _)
xs⊆ys++xs {m = x ∷ m} {n = y ∷ n} {m′ = m′} {n′ = n′} = skip xs⊆ys++xs


-- substitution
_[_/_] : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  {mn : Vec (Use ×′ Use) Γ} {{mn≡ : mn ≡ zip m n}}
  {mnmn′ : Vec (Use ×′ Use) (Γ + Γ′)} {{mnmn′≡ : mnmn′ ≡ zip (m ++ m′) (n ++ n′)}}
  {{σ : Alphabet}}
  → Term m n
  → Term m′ n′
  → (f : Fin Γ)
  → Term (m ++ m′) (n ++ n′)
_[_/_] {_} {_} {m} {n} {m′} {n′} ⦃ mn≡ = refl ⦄ ⦃ mnmn′≡ = refl ⦄ (var x₁) u x =
  {!   !}
  -- weaken-term xs⊆ys++xs u
_[_/_] ⦃ mn≡ = refl ⦄ ⦃ mnmn′≡ = refl ⦄ (agent α ⟨ args ⟩) u x = {!   !}
 