module IntegerMod2 where

open import 1Lab.Type
open import 1Lab.HLevel
open import 1Lab.HLevel.Universe
open import 1Lab.Path
open import Data.Fin
open import Algebra.Ring

ℤ₂ : Type
ℤ₂ = Fin 2

pattern 𝕫₀ = fzero
pattern 𝕫₁ = fsuc fzero

open import Data.Dec

ℤ₂→Fin : ℤ₂ → Fin 2
ℤ₂→Fin 𝕫₀ = fzero
ℤ₂→Fin 𝕫₁ = fsuc fzero

Fin→ℤ₂ : Fin 2 → ℤ₂
Fin→ℤ₂ fzero = 𝕫₀
Fin→ℤ₂ (fsuc fzero) = 𝕫₁

ℤ₂-inverse : ℤ₂ → ℤ₂
ℤ₂-inverse 𝕫₀ = 𝕫₀
ℤ₂-inverse 𝕫₁ = 𝕫₁

ℤ₂-is-set : is-set ℤ₂
ℤ₂-is-set = Fin-is-set

_ℤ₂*_ : ℤ₂ → ℤ₂ → ℤ₂
𝕫₀ ℤ₂* 𝕫₀ = 𝕫₀
𝕫₀ ℤ₂* 𝕫₁ = 𝕫₀
𝕫₁ ℤ₂* 𝕫₀ = 𝕫₀
𝕫₁ ℤ₂* 𝕫₁ = 𝕫₁

_ℤ₂+_ : ℤ₂ → ℤ₂ → ℤ₂
𝕫₀ ℤ₂+ 𝕫₀ = 𝕫₀
𝕫₀ ℤ₂+ 𝕫₁ = 𝕫₁
𝕫₁ ℤ₂+ 𝕫₀ = 𝕫₁
𝕫₁ ℤ₂+ 𝕫₁ = 𝕫₀

ℤ₂*-assoc : {x y z : ℤ₂} → (x ℤ₂* (y ℤ₂* z)) ≡ ((x ℤ₂* y) ℤ₂* z)
ℤ₂*-assoc {𝕫₀} {𝕫₀} {𝕫₀} = refl
ℤ₂*-assoc {𝕫₀} {𝕫₀} {𝕫₁} = refl
ℤ₂*-assoc {𝕫₀} {𝕫₁} {𝕫₀} = refl
ℤ₂*-assoc {𝕫₀} {𝕫₁} {𝕫₁} = refl
ℤ₂*-assoc {𝕫₁} {𝕫₀} {𝕫₀} = refl
ℤ₂*-assoc {𝕫₁} {𝕫₀} {𝕫₁} = refl
ℤ₂*-assoc {𝕫₁} {𝕫₁} {𝕫₀} = refl
ℤ₂*-assoc {𝕫₁} {𝕫₁} {𝕫₁} = refl

ℤ₂+-assoc : {x y z : ℤ₂} → (x ℤ₂+ (y ℤ₂+ z)) ≡ ((x ℤ₂+ y) ℤ₂+ z)
ℤ₂+-assoc {𝕫₀} {𝕫₀} {𝕫₀} = refl
ℤ₂+-assoc {𝕫₀} {𝕫₀} {𝕫₁} = refl
ℤ₂+-assoc {𝕫₀} {𝕫₁} {𝕫₀} = refl
ℤ₂+-assoc {𝕫₀} {𝕫₁} {𝕫₁} = refl
ℤ₂+-assoc {𝕫₁} {𝕫₀} {𝕫₀} = refl
ℤ₂+-assoc {𝕫₁} {𝕫₀} {𝕫₁} = refl
ℤ₂+-assoc {𝕫₁} {𝕫₁} {𝕫₀} = refl
ℤ₂+-assoc {𝕫₁} {𝕫₁} {𝕫₁} = refl

ℤ₂-Ring : Ring lzero
ℤ₂-Ring = el ℤ₂ ℤ₂-is-set , record
  { 1r = 𝕫₁
  ; _*_ = _ℤ₂*_
  ; _+_ = _ℤ₂+_
  ; has-is-ring = record
    { *-monoid = record
      { has-is-semigroup = record
        { has-is-magma = record { has-is-set = ℤ₂-is-set }
        ; associative = λ{ {x} {y} {z} → ℤ₂*-assoc {x} {y} {z} }
        }
      ; idl = λ { {𝕫₀} → refl ; {𝕫₁} → refl }
      ; idr = λ{ {𝕫₀} → refl; {𝕫₁} → refl}
      }
    ; +-group = record
      { has-is-group = record
        { unit = 𝕫₀
        ; inverse = ℤ₂-inverse
        ; has-is-monoid = record
          { has-is-semigroup = record
            { has-is-magma = record { has-is-set = ℤ₂-is-set }
            ; associative = λ{ {x} {y} {z} → ℤ₂+-assoc {x} {y} {z} }
            }
          ; idl = (λ { {𝕫₀} → refl ; {𝕫₁} → refl })
          ; idr = (λ { {𝕫₀} → refl ; {𝕫₁} → refl })
          }
        ; inversel = λ{ {𝕫₀} → refl; {𝕫₁} → refl}
        ; inverser = λ{ {𝕫₀} → refl; {𝕫₁} → refl}
        }
      ; commutes = (λ { {𝕫₀} {𝕫₀} → refl
                      ; {𝕫₀} {𝕫₁} → refl
                      ; {𝕫₁} {𝕫₀} → refl
                      ; {𝕫₁} {𝕫₁} → refl })
      }
    ; *-distribl = λ{ {𝕫₀} {𝕫₀} {𝕫₀} → refl
                    ; {𝕫₀} {𝕫₀} {𝕫₁} → refl
                    ; {𝕫₀} {𝕫₁} {𝕫₀} → refl
                    ; {𝕫₀} {𝕫₁} {𝕫₁} → refl
                    ; {𝕫₁} {𝕫₀} {𝕫₀} → refl
                    ; {𝕫₁} {𝕫₀} {𝕫₁} → refl
                    ; {𝕫₁} {𝕫₁} {𝕫₀} → refl
                    ; {𝕫₁} {𝕫₁} {𝕫₁} → refl }
    ; *-distribr = λ{ {𝕫₀} {𝕫₀} {𝕫₀} → refl
                    ; {𝕫₀} {𝕫₀} {𝕫₁} → refl
                    ; {𝕫₀} {𝕫₁} {𝕫₀} → refl
                    ; {𝕫₀} {𝕫₁} {𝕫₁} → refl
                    ; {𝕫₁} {𝕫₀} {𝕫₀} → refl
                    ; {𝕫₁} {𝕫₀} {𝕫₁} → refl
                    ; {𝕫₁} {𝕫₁} {𝕫₀} → refl
                    ; {𝕫₁} {𝕫₁} {𝕫₁} → refl }
    }
  }

