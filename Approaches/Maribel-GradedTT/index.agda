open import Data.Nat using (ℕ; suc)
open import Data.Fin using (Fin)
open import Data.Fin.Patterns
open import Data.Vec using (Vec; map; foldl; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)
open import Data.Product hiding (map)
open import Function.Base

pattern 1+ n = suc n
pattern 2+ n = 1+ (1+ n)

record Alphabet : Set₁ where
  field
    Agent : Set
    arity : Agent → ℕ
open Alphabet

variable
  n : ℕ

data Term ⦃ σ : Alphabet ⦄ (n : ℕ) : Set where
  var : Fin n → Term n
  agent : (α : Agent σ) → Vec (Term n) (arity σ α) → Term n

-- zero-one-two-many
data M : Set where
  𝟘 𝟙 𝟚 ω : M

_∧_ : M → M → M
𝟘 ∧ p = p
p ∧ 𝟘 = p
𝟚 ∧ 𝟚 = 𝟚
𝟙 ∧ 𝟙 = 𝟙
ω ∧ _ = ω
_ ∧ ω = ω
_ ∧ _ = 𝟚

_+_ : M → M → M
𝟘 + p = p
p + 𝟘 = p
𝟙 + 𝟙 = 𝟚
_ + _ = ω


-- Modality Contexts are snoc-lists
data Conₘ : ℕ → Set where
  ε   : Conₘ 0
  _∙_ : (γ : Conₘ n) → (p : M) → Conₘ (1+ n)
infixl 24 _∙_

data _≈ᶜ_ : (γ δ : Conₘ n) → Set where
  ε : ε ≈ᶜ ε
  _∙_ : {γ δ : Conₘ n} {p q : M} → γ ≈ᶜ δ → p ≡ q → (γ ∙ p) ≈ᶜ (δ ∙ q)

𝟘ᶜ : Conₘ n
𝟘ᶜ {n = 0}    = ε
𝟘ᶜ {n = 1+ n} = 𝟘ᶜ ∙ 𝟘

infixl 35 _,_≔_
_,_≔_ : (γ : Conₘ n) (x : Fin n) (p : M) → Conₘ n
ε , ()                ≔ _
(γ ∙ q) , Fin.zero    ≔ p = γ ∙ p
(γ ∙ q) , (Fin.suc x) ≔ p = (γ , x ≔ p) ∙ q

variable
  ⦃ σ ⦄ : Alphabet
  p q r : M
  γ γ′ δ η θ χ : Conₘ n
  x : Fin n
  t u v w z : Term ⦃ σ ⦄ n

-- Well-usage of variables
data _◂_∈_ : (x : Fin n) (p : M) (γ : Conₘ n) → Set where
  here :                       Fin.zero ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (Fin.suc x) ◂ p ∈ γ ∙ q

_∧ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε ∧ᶜ ε = ε
(γ ∙ p) ∧ᶜ (δ ∙ q) = (γ ∧ᶜ δ) ∙ (p ∧ q)
infixr 43 _∧ᶜ_

_≤ᶜ_ : (γ δ : Conₘ n) → Set
γ ≤ᶜ δ = γ ≈ᶜ γ ∧ᶜ δ
infix  10 _≤ᶜ_

infixr 40 _+ᶜ_
_+ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε +ᶜ ε = ε
(γ ∙ p) +ᶜ (δ ∙ q) = (γ +ᶜ δ) ∙ (p + q)

M⁺ : Set
M⁺ = Σ M (_≢ 𝟘)

data _▸_ ⦃ σ : Alphabet ⦄ {n : ℕ} : (γ : Conₘ n) → Term n → Set where
  sub : γ ▸ t
      → δ ≤ᶜ γ
      → δ ▸ t
  var : (𝟘ᶜ , x ≔ 𝟙) ▸ var x
  agent : (α : Agent σ)
    → (v : Vec (∃₂ _▸_) (arity σ α))
    → foldl _ _+ᶜ_ 𝟘ᶜ (map proj₁ v) ▸ agent α (map (proj₁ ∘ proj₂) v)

open import Data.Unit
σ-trivial : Alphabet
σ-trivial = record
  { Agent = ⊤
  ; arity = λ{tt → 0}
  }
example₁ : _▸_ ⦃ σ-trivial ⦄ ε (agent tt [])
example₁ = agent tt []

instance
  σ-pair : Alphabet
  σ-pair = record
    { Agent = ⊤
    ; arity = λ{tt → 2}
    }

example₂ : ε ∙ 𝟚 ▸ agent tt (var 0F ∷ var 0F ∷ [])
example₂ = agent tt ((-, -, var) ∷ (-, -, var) ∷ [])

example₃ : ε ∙ 𝟙 ∙ 𝟙 ▸ agent tt (var 0F ∷ var 1F ∷ [])
example₃ = agent tt ((-, -, var) ∷ (-, -, var) ∷ [])