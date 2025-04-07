open import Data.Nat using (ℕ; suc; _≤_; z≤n; s≤s) renaming (_+_ to _+ⁿ_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; inject≤) renaming (suc to _+1)
open import Data.Fin.Patterns
open import Data.Vec using (Vec; _∷_; [])
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst)
open import Relation.Nullary.Negation
open import Data.Product hiding (map)
open import Function.Base
open import Alphabet

module _ ⦃ σ : Alphabet ⦄ where
open Alphabet.Alphabet σ

pattern 1+ n = suc n
pattern 2+ n = 1+ (1+ n)
  
variable
  n m l : ℕ
  A B : Set

data Args (A : Set) : ℕ → Set where
  ε   :                           Args A 0        -- Empty context.
  _∙_ : {n : ℕ} → Args A n → A → Args A (1+ n)   -- Context extension.

map : {A B : Set} → (A → B) → Args A n → Args B n
map f ε = ε
map f (args ∙ a) = map f args ∙ f a

foldl : {A B : Set} → (B → A → B) → B → Args A n → B
foldl _⊕_ e ε = e
foldl _⊕_ e (args ∙ a) = foldl _⊕_ (e ⊕ a) args

data All (P : A → Set) : Args A n → Set where
  ε : All P ε
  _∙_ : ∀ {a : A} {args : Args A n} → All P args → P a → All P (args ∙ a)

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  agent : (α : Agent) → Vec (Term n) (arity α) → Term n

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
p∧p≡p {𝟘} = _≡_.refl
p∧p≡p {𝟙} = _≡_.refl
p∧p≡p {𝟚} = _≡_.refl
p∧p≡p {ω} = _≡_.refl

p∧𝟘≡p : ∀ {p} → p ∧ 𝟘 ≡ p
p∧𝟘≡p {𝟘} = _≡_.refl
p∧𝟘≡p {𝟙} = _≡_.refl
p∧𝟘≡p {𝟚} = _≡_.refl
p∧𝟘≡p {ω} = _≡_.refl

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
  p q r : M
  γ γ′ δ η θ χ : Conₘ n
  x y : Fin n
  t u v w z : Term n

≈ᶜ-refl : γ ≈ᶜ γ
≈ᶜ-refl {_} {ε} = ε
≈ᶜ-refl {_} {γ ∙ p} = ≈ᶜ-refl ∙ _≡_.refl

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

-- data _▸_ {n : ℕ} : (γ : Conₘ n) → Term n → Set


-- ▸-agent-args-raw : Vec (∃₂ (_▸_ {n})) l → Vec (Term n) l
-- ▸-agent-args-raw [] = []
-- ▸-agent-args-raw (x ∷ args) = proj₁ (proj₂ x) ∷ ▸-agent-args-raw args

-- data _▸_ where
data _▸_ {n : ℕ} : (γ : Conₘ n) → Term n → Set where
  sub : γ ▸ t
      → δ ≤ᶜ γ
      → δ ▸ t
  var : (𝟘ᶜ , x ≔ 𝟙) ▸ var x
  agent : (α : Agent)
    → (v : Vec (∃₂ _▸_) (arity α))
    -- → {γ : Conₘ n} → { γ≡ : γ ≡ Data.Vec.foldl _ _+ᶜ_ 𝟘ᶜ (Data.Vec.map proj₁ v) }
    -- → {t : Term n} → { t≡ : t ≡ agent α (Data.Vec.map (proj₁ ∘ proj₂) v) }
    -- → γ ▸ t
    → Data.Vec.foldl _ _+ᶜ_ 𝟘ᶜ (Data.Vec.map proj₁ v) ▸ agent α (Data.Vec.map (proj₁ ∘ proj₂) v)

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
  wkArgs : n ≤ m → Vec (Term n) l → Vec (Term m) l
  wkArgs n≤l [] = []
  wkArgs n≤l (t ∷ args) = wk n≤l t ∷ wkArgs n≤l args

  -- wkArgs n≤l args = Data.Vec.map (wk n≤l) args

  wk : n ≤ l → Term n → Term l
  wk n≤l (var x) = var (inject≤ x n≤l)
  wk n≤l (agent α args) = agent α (wkArgs n≤l args)

mutual
  _[_:=_]ᵃ : Vec (Term n) l → Fin n → Term m → Vec (Term (n +ⁿ m)) l
  [] [ x := u ]ᵃ = []
  (t ∷ args) [ x := u ]ᵃ = (t [ x := u ]) ∷ (args [ x := u ]ᵃ)
  
  open import Data.Nat.Properties
  _[_:=_] : Term n → Fin n → Term l → Term (n +ⁿ l)
  var 0F [ 0F := u ] = wk (m≤n⇒m≤1+n (m≤n⇒m≤o+n _ ≤-refl)) u
  var (x +1) [ 0F := u ] = var (x +1 ↑ˡ _)
  var 0F [ y +1 := u ] = var 0F
  var (x +1) [ y +1 := u ] = wk (n≤1+n _) (var x [ y := u ])
  agent α args [ x := u ] = agent α (args [ x := u ]ᵃ)


ω∌𝟘ᶜ : ¬ x ◂ ω ∈ 𝟘ᶜ
ω∌𝟘ᶜ (there ω∈) = ω∌𝟘ᶜ ω∈

𝟘ᶜ-valid : {n : ℕ} → Conₘ-is-valid (𝟘ᶜ {n})
𝟘ᶜ-valid _ = ω∌𝟘ᶜ

ω∌𝟘ᶜ[x≔𝟙] : ¬ x ◂ ω ∈ (𝟘ᶜ , y ≔ 𝟙)
ω∌𝟘ᶜ[x≔𝟙] {_} {0F} {0F} ()
ω∌𝟘ᶜ[x≔𝟙] {_} {0F} {y +1} ()
ω∌𝟘ᶜ[x≔𝟙] {_} {x +1} {0F} (there ω∈) = ω∌𝟘ᶜ ω∈
ω∌𝟘ᶜ[x≔𝟙] {_} {x +1} {y +1} (there ω∈) = ω∌𝟘ᶜ[x≔𝟙] ω∈

𝟘ᶜ[x≔1]-valid : {n : ℕ} → {x : Fin n} → Conₘ-is-valid (𝟘ᶜ {n} , x ≔ 𝟙)
𝟘ᶜ[x≔1]-valid _ = ω∌𝟘ᶜ[x≔𝟙]

-- ≤ᶜ-valid : Conₘ-is-valid γ → γ ≤ᶜ δ → Conₘ-is-valid δ
-- ≤ᶜ-valid γ-ok ρ = {! ρ  !}

wkConₘ : n ≤ m → Conₘ n → Conₘ m
wkConₘ n≤m ε = 𝟘ᶜ
wkConₘ (s≤s n≤m) (γ ∙ p) = (wkConₘ n≤m γ) ∙ p

-- 𝟘ᶜ▸wk-t₀ : {n : ℕ} → (t₀ : Term 0) → (𝟘ᶜ {n}) ▸ wk z≤n t₀
-- 𝟘ᶜ▸wk-t₀ (agent α x) = agent α {!   !}


-- ▸-wk : (n≤m : n ≤ m) → (t : Term n) → ▸ t → ▸ (wk n≤m t)
-- ▸-wk z≤n (agent α x) (ε , γ-ok , γ▸t) = 𝟘ᶜ , 𝟘ᶜ-valid , agent α (Data.Vec.map (λ t₀ → 𝟘ᶜ , (wk z≤n t₀ , 𝟘ᶜ▸wk-t₀ t₀)) x) {_} {{! _≡_.refl  !}} {_} {{!   !}}
-- ▸-wk (s≤s n≤m) (var x) (γ ∙ p , γ-ok , γ▸t) = _ , 𝟘ᶜ[x≔1]-valid , var
-- ▸-wk (s≤s n≤m) (agent α x) (γ ∙ p , γ-ok , sub γ▸t x₁) =
--   let asd = Data.Vec.map (λ x₂ → {!   !}) x
--   in {!   !} , ({!   !} , (agent α asd))
-- ▸-wk (s≤s n≤m) (agent α x) (γ ∙ p , γ-ok , agent α₁ v {_} {as} {_} {_≡_.refl}) =
--   (wkConₘ n≤m γ) ∙ p , {!   !} , agent α (Data.Vec.map (λ{(fst , (fst₁ , snd)) → (wkConₘ (s≤s n≤m) fst) , (wk (s≤s n≤m) fst₁) , {! proj₂ (proj₂ (▸-wk (s≤s n≤m) fst₁ ?))  !}}) v)
--   -- (wkConₘ n≤m γ) ∙ p , {!   !} , agent α {!   !}

≤ᶜ-wk-apply : ∀ {γ δ : Conₘ n} → (ρ : n ≤ m) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
≤ᶜ-wk-apply {_} {_} {ε} {ε} ρ ρᶜ = ≤ᶜ-refl
≤ᶜ-wk-apply {_} {_} {γ ∙ p} {δ ∙ q} (s≤s ρ) (ρᶜ ∙ x) = (≤ᶜ-wk-apply ρ ρᶜ) ∙ x

wk≤𝟘ᶜ[x≔1] : (ρ : n ≤ m) → wkConₘ ρ (𝟘ᶜ , x ≔ 𝟙) ≤ᶜ (𝟘ᶜ , inject≤ x ρ ≔ 𝟙)
wk≤𝟘ᶜ[x≔1] {x = 0F} (s≤s ρ) = γ≤𝟘ᶜ ∙ _≡_.refl
wk≤𝟘ᶜ[x≔1] {x = x +1} (s≤s ρ) = (wk≤𝟘ᶜ[x≔1] ρ) ∙ _≡_.refl


≤ᶜ-wk : ∀ {γ : Conₘ n} → (ρ : n ≤ n) → wkConₘ ρ γ ≤ᶜ γ
≤ᶜ-wk = {!   !}

mutual
  ∃₂-wk : n ≤ m → ∃₂ (_▸_ {n}) → ∃₂ (_▸_ {m})
  ∃₂-wk ρ (γ , t , γ▸t) = wkConₘ ρ γ , wk ρ t , ▸-wk ρ γ▸t

  ▸-wk : (n≤m : n ≤ m) → γ ▸ t → wkConₘ n≤m γ ▸ (wk n≤m t)
  ▸-wk ρ (sub γ▸t γ≤γ′) = sub (▸-wk ρ γ▸t) (≤ᶜ-wk-apply ρ γ≤γ′)
  ▸-wk {1+ n} {1+ m} {γ} {var 0F} (s≤s ρ) var = sub var (γ≤𝟘ᶜ ∙ _≡_.refl)
  ▸-wk {1+ n} {1+ m} {γ} {var (_+1 x)} (s≤s ρ) var = sub var (wk≤𝟘ᶜ[x≔1] ρ ∙ _≡_.refl)
  ▸-wk {n} {m} {γ} {agent α x} ρ (agent .α v) = {! v  !}
  -- ▸-wk {n} {m} {γ} {agent α x} ρ (agent .α v {γ≡ = _≡_.refl} {t≡ = _≡_.refl}) = {!   !}

-- ▸-subst : (t : Term n) (u : Term m) → ▸ t → ▸ u → (x : Fin n) → ▸ (t [ x := u ])
-- ▸-subst (var 0F) u _ ▸u 0F =
--   ▸-wk (m≤n⇒m≤1+n (m≤n⇒m≤o+n _ ≤-refl)) u ▸u
-- ▸-subst (var 0F) u ▸t ▸u (x +1) =
--   -- ▸-wk {!   !} (var 0F) ▸t
--   𝟘ᶜ ∙ 𝟙 , (λ{_ (there ω∈) → ω∌𝟘ᶜ ω∈}) , var
-- ▸-subst (var (y +1)) u ▸t ▸u 0F =
--   _ , (λ{_ (there ω∈) → ω∌𝟘ᶜ[x≔𝟙] ω∈}) , var
-- ▸-subst (var (y +1)) u (γ , γ-ok , γ▸t) ▸u (x +1) =
--   ▸-wk (m≤n⇒m≤1+n ≤-refl) _ (▸-subst (var y) u (_ , 𝟘ᶜ[x≔1]-valid , var) ▸u x)
-- ▸-subst (agent α args) u ▸t ▸u x = {!   !}    