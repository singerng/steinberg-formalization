import Mathlib.Data.PNat.Notation

namespace Steinberg

#check Add

class PosRootSys (Root : Type u) extends ToString Root where
  height : Root → Nat
  isPresent : Root → Bool
  add (r₁ r₂ : Root) : Option Root
  mul : PNat → Root → Option Root
  maker (r : Root) (i : Nat) : Root × Nat × Root × Nat

  -- well-behavedness conditions
  h_add {r₁ r₂ r₃ : Root} :
    add r₁ r₂ = some r₃ → height r₃ = height r₁ + height r₂

  h_mul {c : PNat} {r r' : Root} :
    mul c r = some r' → height r' = c * height r

  h_maker {r : Root} (hr : ¬isPresent r) {i : Nat} (hi : i ≤ height r) :
    isPresent (maker r i).1
    ∧ isPresent (maker r i).2.2.1
    ∧ (maker r i).2.1 ≤ height (maker r i).1
    ∧ (maker r i).2.2.2 ≤ height (maker r i).2.2.1
    ∧ (maker r i).2.1 + (maker r i).2.2.2 = i
    ∧ add (maker r i).1 (maker r i).2.2.1 = r
    /-match maker r i with
    | (r₁, i₁, r₂, i₂) =>
      isPresent r₁ ∧ isPresent r₂ ∧ i₁ ≤ height r₁ ∧ i₂ ≤ height r₂ ∧ i₁ + i₂ = i ∧ add r₁ r₂ = r -/

/-- Applies the `add` operation for a `PosRootSys`. -/
notation r₁ " +? " r₂ => PosRootSys.add r₁ r₂

/-- Applies the `mul` operation for a `PosRootSys`. -/
notation r₁ " *? " r₂ => PosRootSys.mul r₁ r₂

end Steinberg
