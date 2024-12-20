import Mathlib.Data.PNat.Notation

namespace Steinberg

#check Add

class PosRootSys (Root : Type TΦ) extends ToString Root where
  height : Root → Nat
  add (r₁ r₂ : Root) : Option Root
  mul : PNat → Root → Option Root

  -- well-behavedness conditions
  h_add {ζ η θ : Root} :
    add ζ η = some θ → height θ = height ζ + height η

  h_mul {c : PNat} {ζ ζ' : Root} :
    mul c ζ = some ζ' → height ζ' = c * height ζ


-- /-- Applies the `add` operation for a `PosRootSys`. -/
-- notation ζ₁ " +r " ζ₂ => PosRootSys.add ζ₁ ζ₂

-- /-- Applies the `mul` operation for a `PosRootSys`. -/
-- notation c " *r " ζ => PosRootSys.mul c ζ

end Steinberg
