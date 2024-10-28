{-# OPTIONS --backtracking-instance-search #-}
open import Data.Nat using (ℕ; _+_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
open import Relation.Binary.PropositionalEquality using (_≡_; sym; trans)

data Net : ℕ → ℕ → Set

variable
  i o m    : ℕ
  i₁ i₂ i₃ : ℕ
  o₁ o₂ o₃ : ℕ
  m₁ m₂ m₃ : ℕ

  n : Net i o
  a b c k : Net i o

instance
  i≡i+0 : i ≡ i + 0
  i≡i+0 = sym (+-identityʳ _)

  -- i≡+₃ : {i ≡ i₁ + i₂ + i₃} → i ≡ i₁ + (i₂ + i₃)
  -- i≡+₃ {i} {i₁} {i₂} {i₃} {i≡} = trans i≡ (+-assoc i₁ i₂ i₃)
  
  {-# OVERLAPPING i≡i+0 #-}
  

infixl 8 _⨾_
infixl 9 _⊗_
data Net where
  -- underlying category theory constructs
  id : Net i i
  τ : Net 2 2
  _⊗_ : ∀ {i o i₁ i₂ o₁ o₂ : ℕ} → {{i ≡ i₁ + i₂}} → {{o ≡ o₁ + o₂}}
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


pattern id₀ = id {0}
pattern id₁ = id {1}

-- In case you need to display/inspect id's
-- pattern id[_] n = id {n}
-- {-# DISPLAY id {x} = id[_] x #-}

{-# DISPLAY id {0} = id₀ #-}
{-# DISPLAY id {1} = id₁ #-}