open import Data.Nat
open import Data.Fin
open import Data.Sum
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Function.Base hiding (id)

data Tree {v} (A : Set v) : Set v where
  leaf : A → Tree A
  branch : Tree A → Tree A → Tree A

⊎-tree : Tree ℕ → Set
⊎-tree (leaf x) = Fin x
⊎-tree (branch a b) = ⊎-tree a ⊎ ⊎-tree b

Net : (i o : Tree ℕ) → Set
Net i o = ⊎-tree i → ⊎-tree o
 
variable
  i i′ i″ : Tree ℕ
  o o′ o″ : Tree ℕ
  k k′ k″ : Tree ℕ
  f g h : Net i o

infixl 6 _⨾_
_⨾_ :
    Net i k
  → Net   k o
  → Net i   o
a ⨾ b = λ i → b (a i)


infixl 8 _⊗_
_⊗_ :
    Net i o
  → Net i′ o′
  ------------
  → Net (branch i i′) (branch o o′)
_⊗_ = Data.Sum.map

id : ∀ {i : Tree ℕ} → Net i i
id {i} f = f

postulate
  funext : ∀ {a b} {A : Set a} {B : A → Set b}
         {f g : (x : A) → B x}
       → ((x : A) → f x ≡ g x) → f ≡ g

id⊗id : ∀ {i i′ : Tree ℕ} → id {i} ⊗ id {i′} ≡ id {branch i i′}
id⊗id = funext [ (λ _ → refl) , (λ _ → refl) ]

⊗-⨾-distr : ∀ {i o k i′ o′ k′ : Tree ℕ}
  {f₁ : Net i k} {g₁ : Net k o}
  {f₂ : Net i′ k′} {g₂ : Net k′ o′}
  → ((f₁ ⨾ g₁) ⊗ (f₂ ⨾ g₂)) ≡ ((f₁ ⊗ f₂) ⨾ (g₁ ⊗ g₂))
⊗-⨾-distr = funext [ (λ _ → refl) , (λ _ → refl) ]
