open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_)

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