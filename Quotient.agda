{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)

+-identityʳ : ∀ (m : ℕ) → m + 0 ≡ m
+-identityʳ zero = refl
+-identityʳ (suc m) = cong suc (+-identityʳ m)

+-identityˡ : ∀ (m : ℕ) → 0 + m ≡ m
+-identityˡ m = refl

+-assoc : ∀ m n o → (m + n) + o ≡ m + (n + o)
+-assoc zero _ _    = refl
+-assoc (suc m) n o = cong suc (+-assoc m n o)

data Net : ℕ → ℕ → Set
variable
  i o : ℕ
  i₁ i₂ i₃ o₁ o₂ o₃ : ℕ
  k k₁ k₂ p q : ℕ
  n : Net i o

infixl 8 _⨾_
infixl 9 _⊕_[_,_]
data Net where
  -- underlying category theory constructs
  id : ∀ {i} → Net i i
  τ : Net 2 2
  _⊕_[_,_] :
      Net i₁ o₁
    → Net i₂ o₂
    → i ≡ i₁ + i₂
    → o ≡ o₁ + o₂
    ------------
    → Net i o
  _⨾_ : Net i k
    →  Net   k o
    →  Net i   o
  -- generating operations
  ε⁺ : Net 0 1
  ε⁻ : Net 1 0
  δ⁺ : Net 2 1
  δ⁻ : Net 1 2
  ζ⁺ : Net 2 1
  ζ⁻ : Net 1 2
  
  ⨾-id : n ⨾ id ≡ n
  id-⨟ : id ⨾ n ≡ n
  ⨾-assoc : ∀ {a : Net i p} → {b : Net p q} → {c : Net q o}
    → ((a ⨾ b) ⨾ c) ≡ (a ⨾ (b ⨾ c))
  ⊕-assoc :
      {{i≡ : i ≡ i₁ + i₂ + i₃}}
    → {{o≡ : o ≡ o₁ + o₂ + o₃}}
    → {a : Net i₁ o₁}
    → {b : Net i₂ o₂}
    → {c : Net i₃ o₃}
    → ((a ⊕ b [ refl , refl ]) ⊕ c [ i≡ , o≡ ])
      ≡ a ⊕ (b ⊕ c [ refl , refl ]) [ (i≡ ∙ (+-assoc i₁ i₂ i₃)) , (o≡ ∙ (+-assoc o₁ o₂ o₃)) ]

  ⊕-empty : ((n ⊕ (id {0}) [ sym (+-identityʳ i)  , sym (+-identityʳ o) ]) ≡ n)
  empty-⊕ : (((id {0}) ⊕ n [ refl , refl ]) ≡ n)

  ⊕-⨾-dist :
      {{i≡ : i ≡ i₁ + i₂}}
    → {{o≡ : o ≡ o₁ + o₂}}
    → {{k≡ : k ≡ k₁ + k₂}}
    → {a₁ : Net i₁ k₁}
    → {a₂ : Net i₂ k₂}
    → {b₁ : Net k₁ o₁}
    → {b₂ : Net k₂ o₂}
    → (a₁ ⊕ a₂ [ i≡ , k≡ ]) ⨾ (b₁ ⊕ b₂ [ k≡ , o≡ ]) ≡ (a₁ ⨾ b₁) ⊕ (a₂ ⨾ b₂) [ i≡ , o≡ ]
  
  τ-τ : τ ⨾ τ ≡ id
  ⨾-τ : ∀ {a : Net 1 1}
    → id {1} ⊕ a [ refl , refl ] ⨾ τ
    ≡ τ ⨾ a ⊕ id [ refl , refl ]

id₀ : Net 0 0
id₀ = id

id₁ : Net 1 1
id₁ = id

⨁⁺ : ∀ {k} → Net 0 1 → Net 0 k
⨁⁺ {0} net = id₀
⨁⁺ {suc k} net = net ⊕ (⨁⁺ {k} net) [ refl , refl ]

⨁⁻ : ∀ {k} → Net 1 0 → Net k 0
⨁⁻ {0} net = id₀
⨁⁻ {suc k} net = net ⊕ (⨁⁻ {k} net) [ refl , refl ]

infix 5 _⟶_
data _⟶_ : ∀ {i o : ℕ} → Net i o → Net i o → Set where
  ε⁺ : ∀ {n : Net 1 o} → (ε⁺ ⨾ n) ⟶ ⨁⁺ ε⁺
  ε⁻ : ∀ {n : Net i 1} → (n ⨾ ε⁻) ⟶ ⨁⁻ ε⁻
  δ-δ : δ⁺ ⨾ δ⁻ ⟶ τ
  ζ-ζ : ζ⁺ ⨾ ζ⁻ ⟶ τ
  δ-ζ : δ⁺ ⨾ ζ⁻ ⟶ (ζ⁻ ⊕ ζ⁻ [ refl , refl ]) ⨾ ((id₁ ⊕ τ [ refl , refl ]) ⊕ id₁ [ refl , refl ]) ⨾ (δ⁺ ⊕ δ⁺ [ refl , refl ])
  ζ-δ : ζ⁺ ⨾ δ⁻ ⟶ (δ⁻ ⊕ δ⁻ [ refl , refl ]) ⨾ ((id₁ ⊕ τ [ refl , refl ]) ⊕ id₁ [ refl , refl ]) ⨾ (ζ⁺ ⊕ ζ⁺ [ refl , refl ])


ε-ε⟶nothing : ε⁺ ⨾ ε⁻ ⟶ id₀
ε-ε⟶nothing = ε⁺

ε-id-ε⟶nothing : ε⁺ ⨾ id ⨾ ε⁻ ⟶ id₀
ε-id-ε⟶nothing = subst (λ x → x ⨾ ε⁻ ⟶ id₀) (
    ε⁺
  ≡⟨ sym ⨾-id ⟩
    ε⁺ ⨾ id
  ∎) ε-ε⟶nothing

ε⟶≡ : ε⁺ ⨾ ε⁻ ⟶ id₀ ≡ ε⁺ ⨾ id ⨾ ε⁻ ⟶ id₀
ε⟶≡ =
    (ε⁺ ⨾ ε⁻ ⟶ id₀)
  ≡⟨ cong (λ a → a ⨾ ε⁻ ⟶ id₀) (sym ⨾-id) ⟩
    (ε⁺ ⨾ id ⨾ ε⁻ ⟶ id₀)
  ∎
