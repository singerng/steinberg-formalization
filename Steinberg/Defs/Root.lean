import Mathlib.Data.PNat.Notation

namespace Steinberg

#check Add

class PosRootSys (Root : Type u) extends ToString Root where
  height : Root → Nat
  isPresent : Root → Bool
  add (r₁ r₂ : Root) : Option Root
  mul : PNat → Root → Option Root
  maker (ζ : Root) (i : Nat) : Root × Nat × Root × Nat

  -- well-behavedness conditions
  h_add {ζ η θ : Root} :
    add ζ η = some θ → height θ = height ζ + height η

  h_mul {c : PNat} {ζ ζ' : Root} :
    mul c ζ = some ζ' → height ζ' = c * height ζ

  h_maker {ζ : Root} (hr : ¬isPresent ζ) {i : Nat} (hi : i ≤ height ζ) :
    isPresent (maker ζ i).1
    ∧ isPresent (maker ζ i).2.2.1
    ∧ (maker ζ i).2.1 ≤ height (maker ζ i).1
    ∧ (maker ζ i).2.2.2 ≤ height (maker ζ i).2.2.1
    ∧ (maker ζ i).2.1 + (maker ζ i).2.2.2 = i
    ∧ add (maker ζ i).1 (maker ζ i).2.2.1 = ζ

/-- Applies the `add` operation for a `PosRootSys`. -/
notation ζ₁ " +r " ζ₂ => PosRootSys.add ζ₁ ζ₂

/-- Applies the `mul` operation for a `PosRootSys`. -/
notation c " *r " ζ => PosRootSys.mul c ζ

end Steinberg
