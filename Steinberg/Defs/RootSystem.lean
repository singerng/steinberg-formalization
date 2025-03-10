/-

LICENSE goes here.

-/

import Steinberg.Macro.Group

namespace Steinberg

class PosRootSys (Root : semiOutParam (Type TΦ))
  extends
    ToString Root
  where
  height : Root → Nat

attribute [height_simps] PosRootSys.height

open PosRootSys

abbrev SingleSpanRootPair (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] :=
  (ζ : Φ) × (η : Φ) × (θ : Φ) × R ×' (height θ = height ζ + height η)

abbrev DoubleSpanRootPair (Φ : Type TΦ) [PosRootSys Φ] (R : Type TR) [Ring R] := (
  (ζ : Φ) × (η : Φ) × (θ₁ : Φ) × (θ₂ : Φ)
  × R × R ×' (height θ₁ = height ζ + height η) ×' (height θ₂ = height ζ + 2 * height η)
)

end Steinberg
