open import Data.Nat using (ℕ; suc; _+_)
-- open import Data.Nat.Properties
open import Data.Vec hiding ([_]; replicate)
open import Data.List using (List; []; _∷_)
open import Data.Product using (∃-syntax; uncurry′; ∃; _,_; _×_)
open import Data.Empty
open import Data.Maybe using (Maybe; just; nothing)
open import Agda.Builtin.Unit
open import Data.Vec.Relation.Unary.All using (All; all?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; subst; trans; cong)
open import Relation.Nullary.Decidable
open import Agda.Builtin.Sigma
open import Function.Base
open import Agda.Primitive
import Data.Vec.Membership.Propositional as Member
open Member using (_∈_; _∉_)
import Data.Vec.Relation.Unary.Any as Any
open Any using (Any; here; there)
import Data.Fin as Fin
open import Data.Fin.Properties using (suc-injective)

data Use : Set where
  #2 #1 #0 : Use

data Use-Pred : (Use × Use) → Set where
  2↓ : Use-Pred (#2 , #1)
  1↓ : Use-Pred (#1 , #0)

Names : Set
Names = ℕ

-- Multiplicities
M : Names → Set
M = Vec Use

MM : Names → Set
MM = Vec (Use × Use)

CtxTy : Names → Set₁
CtxTy Γ = M Γ → M Γ → Set

record Alphabet : Set₁ where
  field
    AgentTy : Set
    arity : AgentTy → ℕ
open Alphabet


-- sublist
infix 3 _⊆_

data _⊆_ : ∀ {n n′ : ℕ} → MM n → MM n′ → Set  where
  base : [] ⊆ []
  skip : ∀ {n n′ : ℕ} {y : Use} {xs : MM n} {ys : MM n′}
    → xs ⊆ ys → xs ⊆ ((y , y) ∷ ys)
  keep : ∀ {n n′ : ℕ} {x : (Use × Use)} {xs : MM n} {ys : MM n′}
    → xs ⊆ ys → (x ∷ xs) ⊆ (x ∷ ys)

---

data Var : {Γ : Names} → CtxTy Γ where
  here : ∀ {Γ} {m n : M Γ} {x x′}
    → Use-Pred (x , x′)
    → Var (x ∷ m) (x′ ∷ n)
  there : ∀ {Γ} {m n : M Γ} {x}
    → Var m n
    → Var (x ∷ m) (x ∷ n)

pattern here₂ = here 2↓
pattern here₁ = here 1↓

weaken-var : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  → zip m n ⊆ zip m′ n′
  → Var m n
  → Var m′ n′
weaken-var {suc Γ} {suc Γ′} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} (skip sub) var = there (weaken-var sub var)
weaken-var {suc Γ} {suc Γ′} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} (keep sub) (here use) = here use
weaken-var {suc Γ} {suc Γ′} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} (keep sub) (there var) = there (weaken-var sub var)
  

-- strings together a list of a type that require in/out multiplicities
data Scope {{σ : Alphabet}} {Γ : Names} (A : CtxTy Γ) : ℕ → CtxTy Γ where
  [] : ∀ {m} → Scope A 0 m m
  _∷_ : {m k n : M Γ} {l : ℕ}
    → A m k
    → (ctx : Scope A l k n)
    → Scope A (suc l) m n

Vars′ : ∀ {{σ : Alphabet}} {Γ : Names} → ℕ → CtxTy Γ
Vars′ = Scope Var

apply-⊆ : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  → zip m n ⊆ zip m′ n′
  → M Γ
  → M Γ′
apply-⊆ {_} {_} {[]} {[]} {[]} {[]} base [] = []
apply-⊆ {_} {_} {[]} {[]} {x ∷ m′} {.x ∷ n′} (skip sub) [] = x ∷ m′
apply-⊆ {_} {_} {_ ∷ _} {_ ∷ _} {x ∷ _}  {.x ∷ _} (skip sub) (z ∷ k) = x ∷ apply-⊆ sub (z ∷ k)
apply-⊆ {_} {_} {x ∷ _} {y ∷ _} {.x ∷ _} {.y ∷ _} (keep sub) (z ∷ k) = z ∷ apply-⊆ sub k

x⊆x : ∀ {n} (x : MM n) → x ⊆ x
x⊆x [] = base
x⊆x (_ ∷ x) = keep (x⊆x x)

[]⊆ : ∀ {n} (x : M n) → [] ⊆ zip x x
[]⊆ [] = base
[]⊆ (_ ∷ x) = skip ([]⊆ x)

⊆-trans-base : {Γ Γ′ : Names} {m n : M Γ} {m′ n′ : M Γ′} {k : M Γ}
  → (sub : zip m n ⊆ zip m′ n′)
  → zip m k ⊆ zip m′ (apply-⊆ sub k)
⊆-trans-base {_} {_} {[]} {[]} {[]} {[]} {[]} base = base
⊆-trans-base {_} {_} {[]} {[]} {x′ ∷ m′} {_ ∷ _} {[]} (skip sub) = []⊆ (x′ ∷ m′)
⊆-trans-base {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {.x′ ∷ n′} {z ∷ k} (skip sub) = skip (⊆-trans-base sub)
⊆-trans-base {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} {z ∷ k} (keep sub) = keep (⊆-trans-base sub)


⊆-trans-next : {Γ Γ′ : Names} {m n : M Γ} {m′ n′ : M Γ′} {k : M Γ}
  → (sub : zip m n ⊆ zip m′ n′)
  → zip k n ⊆ zip (apply-⊆ sub k) n′
⊆-trans-next {_} {_} {[]} {[]} {[]} {[]} {[]} base = base
⊆-trans-next {_} {_} {[]} {[]} {x′ ∷ m′} {_ ∷ _} {[]} (skip sub) = skip sub
⊆-trans-next {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {.x′ ∷ n′} {z ∷ k} (skip sub) = skip (⊆-trans-next sub)
⊆-trans-next {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} {z ∷ k} (keep sub) = keep (⊆-trans-next sub)

weaken-vars′ : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
  {{σ : Alphabet}} {l}
  → (sub : zip m n ⊆ zip m′ n′)
  → Vars′ l m n
  → Vars′ l m′ n′
weaken-vars′ {_} {_} {[]} {[]} {[]} {[]} sub [] = []
weaken-vars′ {_} {_} {[]} {[]} {x ∷ m′} {y ∷ n′} (skip sub) [] with weaken-vars′ sub []
... | [] = []
weaken-vars′ {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} (skip sub) [] with weaken-vars′ sub []
... | [] = []
weaken-vars′ {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) [] with weaken-vars′ sub []
... | [] = []
weaken-vars′ {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {y′ ∷ n′} (skip sub) (_∷_ {k = z ∷ k} v vars)
  = weaken-var (⊆-trans-base (skip sub)) v ∷ weaken-vars′ (skip (⊆-trans-next sub)) vars
weaken-vars′ {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) (_∷_ {k = z ∷ k} (here v) vars) =
  (weaken-var (keep (⊆-trans-base sub)) (here v)) ∷ (weaken-vars′ (keep (⊆-trans-next sub)) vars)
weaken-vars′ {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) (_∷_ {k = k} (there v) vars) =
  there (weaken-var (⊆-trans-base sub) v) ∷ weaken-vars′ (keep (⊆-trans-next sub)) vars

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

data Term {{σ}} where
  var : ∀ {Γ : Names} {m n : M Γ}
    → Var m n
    → Term m n
  agent_ : ∀ {Γ} {m n : M Γ} {α : AgentTy σ}
    → Agent α m n
    → Term m n
infixl 7 agent_

Alphabet-example : Alphabet
Alphabet-example = record
  { AgentTy = ⊤
  ; arity = λ{tt → 2}
  }

example₁ : Term {{Alphabet-example}} (#2 ∷ []) (#0 ∷ [])
example₁ = agent tt ⟨ var (here 2↓) ∷ var (here {m = []} 1↓) ∷ [] ⟩

example₂ : Term {{Alphabet-example}} (#1 ∷ #1 ∷ []) (#0 ∷ #0 ∷ [])
example₂ = agent tt ⟨ var here₁ ∷ var (there (here {m = []} 1↓)) ∷ [] ⟩

mutual
  weaken-vars : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
    {{σ : Alphabet}} {l}
    → (sub : zip m n ⊆ zip m′ n′)
    → Vars l m n
    → Vars l m′ n′
  weaken-term : ∀ {Γ Γ′} {m n : M Γ} {m′ n′ : M Γ′}
    {{σ : Alphabet}}
    → zip m n ⊆ zip m′ n′
    → Term m n
    → Term m′ n′

  weaken-term sub (var v) = var (weaken-var sub v)
  weaken-term sub (agent α ⟨ args ⟩) = agent α ⟨ weaken-vars sub args ⟩

  weaken-vars {_} {_} {[]} {[]} {[]} {[]} base [] = []
  weaken-vars {_} {_} {[]} {[]} {[]} {[]} base (_∷_ {k = []} (agent ag) vars) = weaken-term base (agent ag) ∷ weaken-vars base vars
  weaken-vars {_} {_} {[]} {[]} {x′ ∷ m′} {.x′ ∷ n′} (skip sub) [] with weaken-vars sub []
  ... | [] = []
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {.x′ ∷ n′} (skip sub) [] with weaken-vars sub []
  ... | [] = []
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.x ∷ n′} (keep sub) [] with weaken-vars sub []
  ... | [] = []
  weaken-vars {_} {_} {[]} {[]} {x′ ∷ m′} {.x′ ∷ n′} (skip sub) (_∷_ {k = []} (agent ag) vars) =
    weaken-term (skip sub) (agent ag) ∷ weaken-vars ([]⊆ (x′ ∷ n′)) vars
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {x′ ∷ m′} {.x′ ∷ n′} (skip sub) (v ∷ vars) =
    weaken-term (⊆-trans-base (skip sub)) v ∷ weaken-vars (⊆-trans-next (skip sub)) vars
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) (var (here v) ∷ vars) =
    var (weaken-var (keep (⊆-trans-base sub)) (here v)) ∷ (weaken-vars (keep (⊆-trans-next sub)) vars)
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) (var (there v) ∷ vars) =
    var (there (weaken-var (⊆-trans-base sub) v)) ∷ weaken-vars (keep (⊆-trans-next sub)) vars
  weaken-vars {_} {_} {x ∷ m} {y ∷ n} {.x ∷ m′} {.y ∷ n′} (keep sub) (_∷_ {k = z ∷ k} (agent ag) vars) =
    (weaken-term (keep (⊆-trans-base sub)) (agent ag)) ∷ weaken-vars (keep (⊆-trans-next sub)) vars
