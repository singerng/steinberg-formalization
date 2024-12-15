import Mathlib.Data.PNat.Notation

namespace Steinberg

/-

Finite set, height function

Objects at play:

  RootSystem (<- a type of roots)
     - Finite set/alphabet of symbols
     - Symbols have a toHeight function -> Nat
     - isPresent
     - add : Root → Root → Option Root
     - axioms:
        - toHeight needs to be well-behaved wrt add

  WBRootSystem (RS)
    - axioms
    - theorems
-/

class PositiveRootSystem (Root : Type u)
    extends ToString Root where
  height : Root → Nat
  isPresent : Root → Bool
  add : Root → Root → Option Root
  mul : PNat → Root → Option Root

  -- well-behavedness conditions
  h_add (r₁ r₂ r₃ : Root) :
    (add r₁ r₂ = some r₃) → height r₃ = height r₁ + height r₂

  h_mul (c : PNat) (r r' : Root) :
    (mul c r = some r') → height r' = c * height r

  -- NS: should be more...

end Steinberg
