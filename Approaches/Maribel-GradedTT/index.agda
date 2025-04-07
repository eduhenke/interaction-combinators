open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s) renaming (_+_ to _+ⁿ_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; inject≤) renaming (suc to _+1)
open import Data.Fin.Patterns
open import Data.Vec using (Vec; _∷_; []; map)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst; refl; cong; subst₂)
open import Relation.Nullary.Negation
open import Data.Product hiding (map)
open import Function.Base hiding (id)
open import Alphabet

module _ ⦃ σ : Alphabet ⦄ where
open Alphabet.Alphabet σ

pattern 1+ n = suc n
pattern 2+ n = 1+ (1+ n)
  
variable
  n m l : ℕ
  A B : Set

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  agent : (α : Agent) → ⦃ l≡ : l ≡ arity α ⦄ → Vec (Term n) l → Term n

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

p∧p≡p : ∀ {p} → p ∧ p ≡ p
p∧p≡p {𝟘} = refl
p∧p≡p {𝟙} = refl
p∧p≡p {𝟚} = refl
p∧p≡p {ω} = refl

p∧𝟘≡p : ∀ {p} → p ∧ 𝟘 ≡ p
p∧𝟘≡p {𝟘} = refl
p∧𝟘≡p {𝟙} = refl
p∧𝟘≡p {𝟚} = refl
p∧𝟘≡p {ω} = refl

_+_ : M → M → M
𝟘 + p = p
p + 𝟘 = p
𝟙 + 𝟙 = 𝟚
_ + _ = ω

data Wk : ℕ → ℕ → Set where
  id    : {n : ℕ}   → Wk n n                    -- η : Γ ≤ Γ.
  step  : {n m : ℕ} → Wk m n → Wk (1+ m) n      -- If η : Γ ≤ Δ then step η : Γ∙A ≤ Δ.
  lift  : {n m : ℕ} → Wk m n → Wk (1+ m) (1+ n) -- If η : Γ ≤ Δ then lift η : Γ∙A ≤ Δ∙A.

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
  p q r : M
  γ γ′ δ η θ χ : Conₘ n
  x y : Fin n
  t u v w z : Term n

≈ᶜ-refl : γ ≈ᶜ γ
≈ᶜ-refl {_} {ε} = ε
≈ᶜ-refl {_} {γ ∙ p} = ≈ᶜ-refl ∙ refl

-- Well-usage of variables
data _◂_∈_ : (x : Fin n) (p : M) (γ : Conₘ n) → Set where
  here :                        0F ◂ p ∈ γ ∙ p
  there : (h : x ◂ p ∈ γ) → (x +1) ◂ p ∈ γ ∙ q

_∧ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε ∧ᶜ ε = ε
(γ ∙ p) ∧ᶜ (δ ∙ q) = (γ ∧ᶜ δ) ∙ (p ∧ q)
infixr 43 _∧ᶜ_

_≤ᶜ_ : (γ δ : Conₘ n) → Set
γ ≤ᶜ δ = γ ≈ᶜ γ ∧ᶜ δ
infix  10 _≤ᶜ_

≤ᶜ-refl : γ ≤ᶜ γ
≤ᶜ-refl {_} {ε} = ε
≤ᶜ-refl {_} {γ ∙ p} = ≤ᶜ-refl ∙ sym p∧p≡p

γ≤𝟘ᶜ : γ ≤ᶜ 𝟘ᶜ
γ≤𝟘ᶜ {_} {ε} = ε
γ≤𝟘ᶜ {_} {γ ∙ p} = γ≤𝟘ᶜ ∙ sym p∧𝟘≡p

infixr 40 _+ᶜ_
_+ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε +ᶜ ε = ε
(γ ∙ p) +ᶜ (δ ∙ q) = (γ +ᶜ δ) ∙ (p + q)

M⁺ : Set
M⁺ = Σ M (_≢ 𝟘)

sumᶜ : Vec (Conₘ n) l → Conₘ n
sumᶜ [] = 𝟘ᶜ
sumᶜ (γ ∷ γs) = γ +ᶜ sumᶜ γs

data _▸_ {n : ℕ} : (γ : Conₘ n) → Term n → Set where
  sub : γ ▸ t
      → δ ≤ᶜ γ
      → δ ▸ t
  var : (𝟘ᶜ , x ≔ 𝟙) ▸ var x
  agent : (α : Agent)
    → ⦃ l≡ : l ≡ arity α ⦄
    → (v : Vec (∃₂ _▸_) l)
    -- → {γ : Conₘ n} → { γ≡ : γ ≡ sumᶜ (Data.Vec.map proj₁ v) }
    -- → {t : Term n} → { t≡ : t ≡ agent α (Data.Vec.map (proj₁ ∘ proj₂) v) }
    -- → γ ▸ t
    → sumᶜ (map proj₁ v) ▸ agent α (map (proj₁ ∘ proj₂) v)

-- open import Data.Unit
-- σ-trivial : Alphabet
-- σ-trivial = record
--   { Agent = ⊤
--   ; arity = λ{tt → 0}
--   }
-- example₁ : _▸_ ⦃ σ-trivial ⦄ ε (agent tt ε)
-- example₁ = agent tt ε

-- instance
--   σ-pair : Alphabet
--   σ-pair = record
--     { Agent = ⊤
--     ; arity = λ{tt → 2}
--     }

-- example₂ : ε ∙ 𝟚 ▸ agent tt (ε ∙ var 0F ∙ var 0F)
-- example₂ = agent tt (ε ∙ (-, -, var) ∙ (-, -, var))

-- example₃ : ε ∙ 𝟙 ∙ 𝟙 ▸ agent tt (ε ∙ var 0F ∙ var 1F)
-- example₃ = agent tt (ε ∙ (-, -, var) ∙ (-, -, var))

Conₘ-is-valid : (γ : Conₘ n) → Set
Conₘ-is-valid γ = ∀ x → ¬ x ◂ ω ∈ γ

-- Well-usage in term
▸_ : Term n → Set
▸ t = ∃ λ γ → Conₘ-is-valid γ × (γ ▸ t)

mutual
  wkArgs : (ρ : Wk m n) (args : Vec (Term n) l) → Vec (Term m) l
  wkArgs ρ [] = []
  wkArgs ρ (t ∷ args) = wk ρ t ∷ wkArgs ρ args

  wkVar : (ρ : Wk m n) (x : Fin n) → Fin m
  wkVar id x = x
  wkVar (step ρ) x = wkVar ρ x +1
  wkVar (lift ρ) 0F = 0F
  wkVar (lift ρ) (x +1) = wkVar ρ x +1
  
  wk : (ρ : Wk m n) (t : Term n) → Term m
  wk ρ (var x) = var (wkVar ρ x)
  wk ρ (agent α args) = agent α (wkArgs ρ args)

Subst : ℕ → ℕ → Set
Subst m n = Fin n → Term m

mutual
  _[_]ᵃ : (args : Vec (Term n) l) (σ : Subst m n) → Vec (Term m) l
  [] [ σ ]ᵃ = []
  (x ∷ args) [ σ ]ᵃ = x [ σ ] ∷ args [ σ ]ᵃ
  
  _[_] : (t : Term n) (σ : Subst m n) → Term m
  var x [ σ ] = σ x
  agent α x [ σ ] = agent α (x [ σ ]ᵃ)


-- ω∌𝟘ᶜ : ¬ x ◂ ω ∈ 𝟘ᶜ
-- ω∌𝟘ᶜ (there ω∈) = ω∌𝟘ᶜ ω∈

-- 𝟘ᶜ-valid : {n : ℕ} → Conₘ-is-valid (𝟘ᶜ {n})
-- 𝟘ᶜ-valid _ = ω∌𝟘ᶜ

-- ω∌𝟘ᶜ[x≔𝟙] : ¬ x ◂ ω ∈ (𝟘ᶜ , y ≔ 𝟙)
-- ω∌𝟘ᶜ[x≔𝟙] {_} {0F} {0F} ()
-- ω∌𝟘ᶜ[x≔𝟙] {_} {0F} {y +1} ()
-- ω∌𝟘ᶜ[x≔𝟙] {_} {x +1} {0F} (there ω∈) = ω∌𝟘ᶜ ω∈
-- ω∌𝟘ᶜ[x≔𝟙] {_} {x +1} {y +1} (there ω∈) = ω∌𝟘ᶜ[x≔𝟙] ω∈

-- 𝟘ᶜ[x≔1]-valid : {n : ℕ} → {x : Fin n} → Conₘ-is-valid (𝟘ᶜ {n} , x ≔ 𝟙)
-- 𝟘ᶜ[x≔1]-valid _ = ω∌𝟘ᶜ[x≔𝟙]

-- -- ≤ᶜ-valid : Conₘ-is-valid γ → γ ≤ᶜ δ → Conₘ-is-valid δ
-- -- ≤ᶜ-valid γ-ok ρ = {! ρ  !}

wkConₘ : (ρ : Wk m n) → Conₘ n → Conₘ m
wkConₘ id γ = γ
wkConₘ (step ρ) γ = wkConₘ ρ γ ∙ 𝟘
wkConₘ (lift ρ) (γ ∙ p) = wkConₘ ρ γ ∙ p

-- -- 𝟘ᶜ▸wk-t₀ : {n : ℕ} → (t₀ : Term 0) → (𝟘ᶜ {n}) ▸ wk z≤n t₀
-- -- 𝟘ᶜ▸wk-t₀ (agent α x) = agent α {!   !}

wk-≤ᶜ : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
wk-≤ᶜ id γ≤δ = γ≤δ
wk-≤ᶜ (step ρ) γ≤δ = (wk-≤ᶜ ρ γ≤δ) ∙ p∧p≡p
wk-≤ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) (γ≤δ ∙ p≤q) = wk-≤ᶜ ρ γ≤δ ∙ p≤q

wk-𝟘ᶜ : (ρ : Wk m n) → wkConₘ ρ 𝟘ᶜ ≡ 𝟘ᶜ
wk-𝟘ᶜ id = refl
wk-𝟘ᶜ (step ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)
wk-𝟘ᶜ (lift ρ) = cong (λ γ → γ ∙ 𝟘) (wk-𝟘ᶜ ρ)

wk-+ᶜ : (ρ : Wk m n) → wkConₘ ρ (γ +ᶜ δ) ≡ wkConₘ ρ γ +ᶜ wkConₘ ρ δ
wk-+ᶜ id = refl
wk-+ᶜ {γ = γ} {δ = δ} (step ρ) rewrite wk-+ᶜ {γ = γ} {δ = δ} ρ = refl
wk-+ᶜ {γ = γ ∙ p} {δ ∙ q} (lift ρ) rewrite wk-+ᶜ {γ = γ} {δ = δ} ρ = refl

wkUsageVar : (ρ : Wk m n) → (x : Fin n)
           → wkConₘ ρ (𝟘ᶜ , x ≔ p) ≡ 𝟘ᶜ , wkVar ρ x ≔ p
wkUsageVar id x = refl
wkUsageVar (step ρ) x = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)
wkUsageVar (lift ρ) 0F = cong (λ γ → γ ∙ _) (wk-𝟘ᶜ ρ)
wkUsageVar (lift ρ) (x +1) = cong (λ γ → γ ∙ 𝟘) (wkUsageVar ρ x)

wkUsage : (ρ : Wk m n) → γ ▸ t → wkConₘ ρ γ ▸ wk ρ t
wkUsage ρ var = subst (λ γ → γ ▸ wk ρ (var _)) (sym (wkUsageVar ρ _)) var
wkUsage ρ (sub γ▸t x) = sub (wkUsage ρ γ▸t) (wk-≤ᶜ ρ x)
wkUsage ρ (agent α v) =
  subst₂ _▸_ (γ=γ′ ρ v) (cong (agent α) (t≡t′ ρ v)) (agent α (walk ρ v))
  where
    walk : (ρ : Wk m n) → Vec (∃₂ (_▸_ {n})) l → Vec (∃₂ (_▸_ {m})) l
    walk ρ [] = []
    walk ρ ((γ , t , γ▸t) ∷ v) = (wkConₘ ρ γ , wk ρ t , wkUsage ρ γ▸t) ∷ walk ρ v

    γ=γ′ : ∀ {l n m} (ρ : Wk m n) (v : Vec _ l) → sumᶜ (map proj₁ (walk ρ v)) ≡ wkConₘ ρ (sumᶜ (map proj₁ v))
    γ=γ′ ρ [] = sym (wk-𝟘ᶜ ρ)
    γ=γ′ ρ ((γ , t , γ▸t) ∷ v) rewrite wk-+ᶜ {γ = γ} {δ = sumᶜ (map proj₁ v)} ρ = cong (_ +ᶜ_) (γ=γ′ ρ v)

    t≡t′ : ∀ {l n m} (ρ : Wk m n) (v : Vec _ l) → map (proj₁ ∘ proj₂) (walk ρ v) ≡ wkArgs ρ (map (proj₁ ∘ proj₂) v)
    t≡t′ ρ [] = refl
    t≡t′ ρ ((γ , t , γ▸t) ∷ v) rewrite t≡t′ ρ v = refl

-- -- ▸-subst : (t : Term n) (u : Term m) → ▸ t → ▸ u → (x : Fin n) → ▸ (t [ x := u ])
-- -- ▸-subst (var 0F) u _ ▸u 0F =
-- --   ▸-wk (m≤n⇒m≤1+n (m≤n⇒m≤o+n _ ≤-refl)) u ▸u
-- -- ▸-subst (var 0F) u ▸t ▸u (x +1) =
-- --   -- ▸-wk {!   !} (var 0F) ▸t
-- --   𝟘ᶜ ∙ 𝟙 , (λ{_ (there ω∈) → ω∌𝟘ᶜ ω∈}) , var
-- -- ▸-subst (var (y +1)) u ▸t ▸u 0F =
-- --   _ , (λ{_ (there ω∈) → ω∌𝟘ᶜ[x≔𝟙] ω∈}) , var
-- -- ▸-subst (var (y +1)) u (γ , γ-ok , γ▸t) ▸u (x +1) =
-- --   ▸-wk (m≤n⇒m≤1+n ≤-refl) _ (▸-subst (var y) u (_ , 𝟘ᶜ[x≔1]-valid , var) ▸u x)
-- -- ▸-subst (agent α args) u ▸t ▸u x = {!   !}    