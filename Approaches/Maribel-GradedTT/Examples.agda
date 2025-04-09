open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Vec
open import Alphabet
open import Modality
open import Data.Fin
open import Data.Fin.Patterns
open import Data.Product

σ-trivial : Alphabet
σ-trivial = record
  { Agent = ⊤
  ; arity = λ{tt → 0}
  }

instance
  σ-pair : Alphabet
  σ-pair = record
    { Agent = ⊤
    ; arity = λ{tt → 2}
    }

open import index

example₁ : _▸_ ⦃ σ-trivial ⦄ ε (tt ⟨ [] ⟩)
example₁ = agent tt []

example₂ : ε ∙ 𝟚 ▸ tt ⟨ var 0F ∷ var 0F ∷ [] ⟩
example₂ = agent tt ((-, -, var) ∷ (-, -, var) ∷ [])

example₃ : ε ∙ 𝟙 ∙ 𝟙 ▸ tt ⟨ var 1F ∷ var 0F ∷ [] ⟩
example₃ = agent tt ((-, -, var) ∷ (-, -, var) ∷ [])
