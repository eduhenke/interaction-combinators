open import Data.Nat using (ℕ; suc) renaming (_+_ to _+ⁿ_)
open import Data.Fin using (Fin; _↑ˡ_; _↑ʳ_; inject≤) renaming (suc to _+1)
open import Data.Fin.Patterns
open import Data.Vec using (Vec; _∷_; []; map; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; sym; subst; refl; cong; subst₂; trans; cong₂)
open import Relation.Nullary.Negation
open import Data.Product hiding (map; _<*>_)
open import Function.Base hiding (id; _⟨_⟩_)
open import Data.Vec.Relation.Binary.Pointwise.Inductive using (Pointwise)
open Pointwise
open import Alphabet
open import Modality using (Zero-one-twice-many; zero-one-twice-many-modality)
open Zero-one-twice-many using (𝟚)
open import Graded.Modality Zero-one-twice-many using () renaming (Modality to Modalityᵍ)
open Modalityᵍ zero-one-twice-many-modality
open import Graded.Modality.Properties zero-one-twice-many-modality

module _ ⦃ alphabet : Alphabet ⦄ where
open Alphabet.Alphabet alphabet

M : Set
M = Zero-one-twice-many

pattern 1+ n = suc n
pattern 2+ n = 1+ (1+ n)
  
variable
  n m l l′ k : ℕ
  A B : Set

data Term (n : ℕ) : Set where
  var : Fin n → Term n
  _⟨_⟩ : (α : Agent) → ⦃ l≡ : l ≡ arity α ⦄ → (args : Vec (Term n) l) → Term n

infixl 40 _⟨_⟩

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
  γ γ′ δ δ′ η θ χ : Conₘ n
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
≤ᶜ-refl {_} {γ ∙ p} = ≤ᶜ-refl ∙ ≤-refl


p≤𝟘 : p ≤ 𝟘
p≤𝟘 {Zero-one-twice-many.𝟘} = refl
p≤𝟘 {Zero-one-twice-many.𝟙} = refl
p≤𝟘 {Zero-one-twice-many.𝟚} = refl
p≤𝟘 {Zero-one-twice-many.ω} = refl

γ≤𝟘ᶜ : γ ≤ᶜ 𝟘ᶜ
γ≤𝟘ᶜ {_} {ε} = ε
γ≤𝟘ᶜ {_} {γ ∙ p} = γ≤𝟘ᶜ ∙ p≤𝟘

infixr 40 _+ᶜ_
_+ᶜ_ : (γ δ : Conₘ n) → Conₘ n
ε +ᶜ ε = ε
(γ ∙ p) +ᶜ (δ ∙ q) = (γ +ᶜ δ) ∙ (p + q)

M⁺ : Set
M⁺ = Σ M (_≢ 𝟘)

sumᶜ : Vec (Conₘ n) l → Conₘ n
sumᶜ [] = 𝟘ᶜ
sumᶜ (γ ∷ γs) = γ +ᶜ sumᶜ γs

-- Well-usage
data _▸_ {n : ℕ} : (γ : Conₘ n) → Term n → Set where
  sub : γ ▸ t
      → δ ≤ᶜ γ
      → δ ▸ t
  var : (𝟘ᶜ , x ≔ 𝟙) ▸ var x
  agent : {γs : Vec (Conₘ n) l} {ts : Vec (Term n) l}
    → (α : Agent)
    → ⦃ l≡ : l ≡ arity α ⦄
    → (args : Pointwise _▸_ γs ts)
    → sumᶜ γs ▸ α ⟨ ts ⟩

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
  wk ρ (α ⟨ args ⟩) = α ⟨ wkArgs ρ args ⟩

Subst : ℕ → ℕ → Set
Subst m n = Fin n → Term m

variable
  σ : Subst m n

mutual
  _[_]ᵃ : (args : Vec (Term n) l) (σ : Subst m n) → Vec (Term m) l
  [] [ σ ]ᵃ = []
  (x ∷ args) [ σ ]ᵃ = x [ σ ] ∷ args [ σ ]ᵃ
  
  infix 25 _[_]
  _[_] : (t : Term n) (σ : Subst m n) → Term m
  var x [ σ ] = σ x
  α ⟨ x ⟩ [ σ ] = α ⟨ x [ σ ]ᵃ ⟩

wkConₘ : (ρ : Wk m n) → Conₘ n → Conₘ m
wkConₘ id γ = γ
wkConₘ (step ρ) γ = wkConₘ ρ γ ∙ 𝟘
wkConₘ (lift ρ) (γ ∙ p) = wkConₘ ρ γ ∙ p

wk-≤ᶜ : (ρ : Wk m n) → γ ≤ᶜ δ → wkConₘ ρ γ ≤ᶜ wkConₘ ρ δ
wk-≤ᶜ id γ≤δ = γ≤δ
wk-≤ᶜ (step ρ) γ≤δ = (wk-≤ᶜ ρ γ≤δ) ∙ refl
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
wkUsage ρ (agent {_} {γs} {ts} α v) =
  subst₂ _▸_ (γ=γ′ ρ γs) refl (agent α (walk ρ v))
  where
    walk : ∀ {n l} {γs : Vec (Conₘ n) l} {ts : Vec (Term n) l} → (ρ : Wk m n) → Pointwise _▸_ γs ts → Pointwise _▸_ (map (wkConₘ ρ) γs) (wkArgs ρ ts)
    walk ρ [] = []
    walk ρ (γ▸t ∷ v) = wkUsage ρ γ▸t ∷ walk ρ v

    γ=γ′ : ∀ {n l} (ρ : Wk m n) (γs : Vec (Conₘ n) l) → sumᶜ (map (wkConₘ ρ) γs) ≡ wkConₘ ρ (sumᶜ γs)
    γ=γ′ ρ [] = sym (wk-𝟘ᶜ ρ)
    γ=γ′ ρ (γ ∷ γs) rewrite wk-+ᶜ {γ = γ} {δ = sumᶜ γs} ρ = cong (_ +ᶜ_) (γ=γ′ ρ γs)

    -- t≡t′ : ∀ {n l} (ρ : Wk m n) (ts : Vec (Term n) l) → map (wk ρ) ts ≡ wkArgs ρ ts
    -- t≡t′ ρ [] = refl
    -- t≡t′ ρ (t ∷ ts) rewrite t≡t′ ρ ts = refl

infixr 45 _·ᶜ_
_·ᶜ_ : (p : M) (γ : Conₘ n) → Conₘ n
p ·ᶜ ε = ε
p ·ᶜ (γ ∙ q) = (p ·ᶜ γ) ∙ (p · q)

data Substₘ : (m n : ℕ) → Set where
  []  : Substₘ m 0
  _⊙_ : Substₘ m n → Conₘ m → Substₘ m (1+ n)

variable
  Ψ Φ : Substₘ m n

-- Application of substitution matrix from the right

infixl 50 _<*_
_<*_ : (γ : Conₘ n) → (Ψ : Substₘ m n) → Conₘ m
ε <* [] = 𝟘ᶜ
(γ ∙ p) <* (Ψ ⊙ δ) = (p ·ᶜ δ) +ᶜ (γ <* Ψ)

substₘ : (Ψ : Substₘ m n) → (γ : Conₘ n) → Conₘ m
substₘ Ψ γ = γ <* Ψ

-- Composition of substitution matrices

_<*>_ : (Ψ : Substₘ m k) (Φ : Substₘ k n) → Substₘ m n
Ψ <*> [] = []
Ψ <*> (Φ ⊙ δ) = (Ψ <*> Φ) ⊙ (δ <* Ψ)

-- Well-formed modality substitutions: if ∀ x. γ_x ▸ σ x, where
-- γ_x is the x-th row vector of Ψ, then Ψ ▶ σ.

_▶_ : Substₘ m n → Subst m n → Set
_▶_ {n = n} Ψ σ =
  (x : Fin n) → ((𝟘ᶜ , x ≔ 𝟙) <* Ψ) ▸ σ x

·ᶜ-monotoneˡ : p ≤ q → p ·ᶜ γ ≤ᶜ q ·ᶜ γ
·ᶜ-monotoneˡ {γ = ε}     p≤q = ≤ᶜ-refl
·ᶜ-monotoneˡ {γ = γ ∙ r} p≤q = (·ᶜ-monotoneˡ p≤q) ∙ (·-monotoneˡ p≤q)

≤ᶜ-trans : γ ≤ᶜ δ → δ ≤ᶜ η → γ ≤ᶜ η
≤ᶜ-trans {γ = ε}     {δ = ε}     {η = ε}     _           _           = ε
≤ᶜ-trans {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) (δ≤η ∙ q≤r) =
  (≤ᶜ-trans γ≤δ δ≤η) ∙ (≤-trans p≤q q≤r)

+ᶜ-monotoneˡ : γ ≤ᶜ δ → γ +ᶜ η ≤ᶜ δ +ᶜ η
+ᶜ-monotoneˡ {γ = ε}     {δ = ε}     {η = ε}     ε           = ≤ᶜ-refl
+ᶜ-monotoneˡ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ _} (γ≤δ ∙ p≤q) =
  +ᶜ-monotoneˡ γ≤δ ∙ +-monotoneˡ p≤q

-- Addition on the right is monotone
-- If γ ≤ᶜ δ then η +ᶜ γ ≤ᶜ η +ᶜ δ

+ᶜ-monotoneʳ : γ ≤ᶜ δ → η +ᶜ γ ≤ᶜ η +ᶜ δ
+ᶜ-monotoneʳ {γ = ε}     {δ = ε}     {η = ε}     ε           = ≤ᶜ-refl
+ᶜ-monotoneʳ {γ = _ ∙ _} {δ = _ ∙ _} {η = _ ∙ p} (γ≤δ ∙ p≤q) =
  +ᶜ-monotoneʳ γ≤δ ∙ +-monotoneʳ {r = p} p≤q

-- Addition is monotone
-- If γ ≤ᶜ γ′ and δ ≤ᶜ δ′ then γ + δ ≤ᶜ γ′ +ᶜ δ′

+ᶜ-monotone : γ ≤ᶜ γ′ → δ ≤ᶜ δ′ → γ +ᶜ δ ≤ᶜ γ′ +ᶜ δ′
+ᶜ-monotone γ≤γ′ δ≤δ′ = ≤ᶜ-trans (+ᶜ-monotoneˡ γ≤γ′) (+ᶜ-monotoneʳ δ≤δ′)

<*-monotone : {γ δ : Conₘ n} (Ψ : Substₘ m n) → γ ≤ᶜ δ → γ <* Ψ ≤ᶜ δ <* Ψ
<*-monotone {γ = ε}     {δ = ε}     []      γ≤δ         = ≤ᶜ-refl
<*-monotone {γ = _ ∙ _} {δ = _ ∙ _} (Ψ ⊙ η) (γ≤δ ∙ p≤q) =
  +ᶜ-monotone (·ᶜ-monotoneˡ p≤q) (<*-monotone Ψ γ≤δ)

·ᶜ-zeroˡ : (γ : Conₘ n) → 𝟘 ·ᶜ γ ≡ 𝟘ᶜ
·ᶜ-zeroˡ  ε      = refl
·ᶜ-zeroˡ (γ ∙ p) rewrite ·ᶜ-zeroˡ γ = refl

+ᶜ-identityˡ : (γ : Conₘ n) → 𝟘ᶜ +ᶜ γ ≡ γ
+ᶜ-identityˡ  ε      = refl
+ᶜ-identityˡ (γ ∙ p) rewrite +ᶜ-identityˡ γ = refl

<*-zeroˡ : (Ψ : Substₘ m n) → 𝟘ᶜ <* Ψ ≡ 𝟘ᶜ
<*-zeroˡ []      = refl
<*-zeroˡ (Ψ ⊙ γ) rewrite ·ᶜ-zeroˡ γ | <*-zeroˡ Ψ  = +ᶜ-identityˡ 𝟘ᶜ

·ᶜ-distribʳ-+ᶜ : (p q : M) → (γ : Conₘ n) → (p + q) ·ᶜ γ ≡ (p ·ᶜ γ) +ᶜ (q ·ᶜ γ)
·ᶜ-distribʳ-+ᶜ p q  ε      = refl
·ᶜ-distribʳ-+ᶜ p q (γ ∙ r) rewrite ·ᶜ-distribʳ-+ᶜ p q γ | ·-distribʳ-+ r p q = refl

+ᶜ-comm : (γ δ : Conₘ n) → γ +ᶜ δ ≡ δ +ᶜ γ
+ᶜ-comm ε ε = refl
+ᶜ-comm (γ ∙ p) (δ ∙ q) rewrite +ᶜ-comm γ δ | +-comm p q = refl

+ᶜ-assoc : (γ δ η : Conₘ n) → (γ +ᶜ δ) +ᶜ η ≡ γ +ᶜ (δ +ᶜ η)
+ᶜ-assoc ε ε ε = refl
+ᶜ-assoc (γ ∙ p) (δ ∙ q) (η ∙ r) rewrite +ᶜ-assoc γ δ η | +-assoc p q r = refl

<*-distrib-+ᶜ : (Ψ : Substₘ m n) (γ δ : Conₘ n) → (γ +ᶜ δ) <* Ψ ≡ γ <* Ψ +ᶜ δ <* Ψ
<*-distrib-+ᶜ []       ε       ε      = sym (+ᶜ-identityˡ 𝟘ᶜ)
<*-distrib-+ᶜ (Ψ ⊙ η) (γ ∙ p) (δ ∙ q) = begin
  ((γ ∙ p) +ᶜ (δ ∙ q)) <* (Ψ ⊙ η)
    ≡⟨ cong₂ _+ᶜ_ (·ᶜ-distribʳ-+ᶜ p q η) (<*-distrib-+ᶜ Ψ γ δ) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ γ <* Ψ +ᶜ δ <* Ψ
    ≡⟨ cong (_ +ᶜ_) (+ᶜ-comm (γ <* Ψ) (δ <* Ψ)) ⟩
  (p ·ᶜ η +ᶜ q ·ᶜ η) +ᶜ δ <* Ψ +ᶜ γ <* Ψ
    ≡⟨ +ᶜ-assoc (p ·ᶜ η) (q ·ᶜ η) (δ <* Ψ +ᶜ γ <* Ψ) ⟩
  p ·ᶜ η +ᶜ q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ
    ≡⟨ +ᶜ-comm (p ·ᶜ η) (q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ) ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ) +ᶜ p ·ᶜ η
    ≡⟨ +ᶜ-assoc _ _ _ ⟩
  q ·ᶜ η +ᶜ (δ <* Ψ +ᶜ γ <* Ψ) +ᶜ p ·ᶜ η
    ≡⟨ cong (_ +ᶜ_) (+ᶜ-assoc (δ <* Ψ) (γ <* Ψ) (p ·ᶜ η)) ⟩
  q ·ᶜ η +ᶜ δ <* Ψ +ᶜ γ <* Ψ +ᶜ p ·ᶜ η
    ≡⟨ sym (+ᶜ-assoc _ _ _) ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ) +ᶜ γ <* Ψ +ᶜ p ·ᶜ η
    ≡⟨ cong (_ +ᶜ_) (+ᶜ-comm (γ <* Ψ) (p ·ᶜ η)) ⟩
  (q ·ᶜ η +ᶜ δ <* Ψ) +ᶜ p ·ᶜ η +ᶜ γ <* Ψ
    ≡⟨ +ᶜ-comm _ _ ⟩
  ((p ·ᶜ η +ᶜ γ <* Ψ) +ᶜ q ·ᶜ η +ᶜ δ <* Ψ) ∎
  where
  open import Relation.Binary.Reasoning.Syntax
  open Relation.Binary.PropositionalEquality.≡-Reasoning

substₘ-lemma :
  (Ψ : Substₘ m n) →
  Ψ ▶ σ → γ ▸ t → substₘ Ψ γ ▸ t [ σ ]
substₘ-lemma Ψ Ψ▶σ var = Ψ▶σ _
substₘ-lemma Ψ Ψ▶σ (sub γ▸t x) = sub (substₘ-lemma Ψ Ψ▶σ γ▸t) (<*-monotone Ψ x)
substₘ-lemma Ψ Ψ▶σ (agent {_} {γs} {ts} α v) =
  subst₂ _▸_ (γ=γ′ Ψ Ψ▶σ γs) refl (agent α (walk Ψ Ψ▶σ v))
  where
    walk : ∀ {n l σ} {γs : Vec (Conₘ n) l} {ts : Vec (Term n) l} → (Ψ : Substₘ m n) (Ψ▶σ : Ψ ▶ σ)
      → Pointwise _▸_ γs ts → Pointwise _▸_ (map (substₘ Ψ) γs) (ts [ σ ]ᵃ)
    walk Ψ Ψ▶σ [] = []
    walk Ψ Ψ▶σ (γ▸t ∷ v) = substₘ-lemma Ψ Ψ▶σ γ▸t ∷ walk Ψ Ψ▶σ v

    γ=γ′ : ∀ {n l σ} (Ψ : Substₘ m n) (Ψ▶σ : Ψ ▶ σ) (γs : Vec (Conₘ n) l)
      → sumᶜ (map (substₘ Ψ) γs) ≡ substₘ Ψ (sumᶜ γs)
    γ=γ′ Ψ Ψ▶σ [] = sym (<*-zeroˡ Ψ)
    γ=γ′ Ψ Ψ▶σ (γ ∷ γs) rewrite <*-distrib-+ᶜ Ψ γ (sumᶜ γs) = cong (_ +ᶜ_) (γ=γ′ Ψ Ψ▶σ γs)

-- data Equation {n : ℕ} : (t u : Term n) → Set where
--   _＝_ : (t u : Term n) → Equation t u
--   eq-sym : Equation t u → Equation u t

-- -- Rule
-- record _⋈_ (α β : Agent) : Set where
--   field
--     {nʳ} : ℕ
--     lhs : Vec (Term nʳ) (arity α)
--     rhs : Vec (Term nʳ) (arity β)
--     γs : Vec (Conₘ nʳ) (arity α +ⁿ arity β)
--     γs▸ts : Pointwise _▸_ γs (lhs ++ rhs)
--     well-used : ∀ x → x ◂ 𝟚 ∈ sumᶜ γs

-- record Configuration : Set where
--   field
--     rules : ∀ α β → α ⋈ β
--     {nᶜ lʰ lᵉ} : ℕ
--     head : Vec (Term nᶜ) lʰ
--     body : Vec (∃₂ (Equation {nᶜ})) lᵉ
--     γsʰ : Vec (Conₘ nᶜ) lʰ
--     γsᵇ : Vec (Conₘ nᶜ × Conₘ nᶜ) lᵉ
--     γsʰ▸head : Pointwise _▸_ γsʰ head
--     γsᵇ▸body : Pointwise (λ{(γ , δ) (t , u , _) → γ ▸ t × δ ▸ u}) γsᵇ body
  
--   γʰ = sumᶜ γsʰ
--   γᵇ = sumᶜ (map (uncurry _+ᶜ_) γsᵇ)
--   γᶜ = γʰ +ᶜ γᵇ

--   field
--     well-used : Conₘ-is-valid γᶜ 