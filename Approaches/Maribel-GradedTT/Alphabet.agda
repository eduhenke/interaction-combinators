open import Data.Nat

record Alphabet : Set₁ where
  field
    Agent : Set
    arity : Agent → ℕ