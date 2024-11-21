quotRem : ∀ {m} n → Fin (m * n) → Fin n × Fin m
quotRem {suc m} n i = [ (_, fzero) , ×-map₂ fsuc ∘ quotRem {m} n ] (split-+ i)

remQuot : ∀ {m} n → Fin (m * n) → Fin m × Fin n
remQuot i = ×-swap .fst ∘ quotRem i

quotient : ∀ {m} n → Fin (m * n) → Fin m
quotient n = fst ∘ remQuot n

remainder : ∀ {m} n → Fin (m * n) → Fin n
remainder {m} n = snd ∘ remQuot {m} n

-- Next in progression after splitAt and remQuot
finToFun : ∀ {m n : Nat} → Fin (m ^ n) → (Fin n → Fin m)
finToFun {m} {suc n} i fzero    = quotient (m ^ n) i
finToFun {m} {suc n} i (fsuc j) = finToFun (remainder {m} (m ^ n) i) j

-- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
infixl 5 _↑ˡ_
_↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m Data.Nat.+ n)
fzero    ↑ˡ n = fzero
(fsuc i) ↑ˡ n = fsuc (i ↑ˡ n)

-- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
infixr 5 _↑ʳ_
_↑ʳ_ : ∀ {m} n → Fin m → Fin (n Data.Nat.+ m)
zero    ↑ʳ i = i
(suc n) ↑ʳ i = fsuc (n ↑ʳ i)

-- inverse of remQuot
combine : ∀ {m n} → Fin m → Fin n → Fin (m * n)
combine {suc m} {n} fzero    j = j ↑ˡ (m * n)
combine {suc m} {n} (fsuc i) j = n ↑ʳ (combine i j)

-- -- inverse of above function
-- funToFin : ∀ {m n} → (Fin m → Fin n) → Fin (n ^ m)
-- funToFin {zero}  f = fzero
-- funToFin {suc m} f = combine (f fzero) (funToFin (f ∘ fsuc))

-- -- injection on the left: "i" ↑ˡ n = "i" in Fin (m + n)
-- infixl 5 _↑ˡ_
-- _↑ˡ_ : ∀ {m} → Fin m → ∀ n → Fin (m + n)
-- fzero    ↑ˡ n = fzero
-- (fsuc i) ↑ˡ n = fsuc (i ↑ˡ n)

-- -- injection on the right: n ↑ʳ "i" = "n + i" in Fin (n + m)
-- infixr 5 _↑ʳ_
-- _↑ʳ_ : ∀ {m} n → Fin m → Fin (n + m)
-- zero    ↑ʳ i = i
-- (suc n) ↑ʳ i = fsuc (n ↑ʳ i)

join : ∀ m n → Fin m ⊎ Fin n → Fin (m + n)
join m n = [ _↑ˡ n , m ↑ʳ_ ]

-- Fin-^↔→ : ∀ {m n : Nat} → Iso (Fin (m ^ n)) (Fin n → Fin m)
-- Fin-^↔→ = finToFun , iso funToFin
--   (λ x → ap fst {!   !})
--   {!   !}
