open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_;_^_)
open import Data.Nat.Properties using (+-assoc; +-identityˡ; +-identityʳ)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym)
open import Data.Fin.Base using (Fin)
open import Data.List
open import Relation.Binary using (IsEquivalence; Setoid)
open import Data.Fin.Permutation using (Permutation; transpose; flip; _∘ₚ_) renaming (id to permutationId)
open import Data.Fin.Patterns
open import Data.Product using (_×_)

D : Set
D = ℕ

unit : D
unit = 0

⟨_,_⟩ : D → D → D
⟨ a , b ⟩ = a + b

[_,_] : D → D → D
[ a , b ] = a * b

companion : ∀ {a b c d : D} → ⟨ [ a , b ] , [ c , d ] ⟩ ≡ [ ⟨ a , c ⟩ , ⟨ b , d ⟩ ]
companion = {!   !}