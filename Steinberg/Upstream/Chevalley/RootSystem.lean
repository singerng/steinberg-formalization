

import Mathlib.Data.Matrix.Basic

import Steinberg.Upstream.Chevalley.IndicatorMatrix
import Steinberg.Upstream.Chevalley.ZSigned
import Steinberg.Upstream.Chevalley.BoolToRing

namespace Chevalley

/-- Typeclass for root systems. See `ARoot`, `BRoot`, `CRoot`, and `DRoot` for examples.
  TODO: Encode "additive structure" of roots. -/
class RootSystem (Φ : Type TΦ) where
  neg : Φ → Φ
  neg_of_neg : ∀ (ζ : Φ), neg (neg ζ) = ζ

open RootSystem

class ChevalleyRealization (Φ : Type TΦ) [RootSystem Φ] (I' : Type TI) [DecidableEq I'] [Fintype I'] (R : Type TR) [CommRing R]
  where
  M : Φ → R → Matrix.GeneralLinearGroup I' R
  n (ζ : Φ) (t : Rˣ) := (M ζ t.val) * (M (neg ζ) (-t.inv)) * (M ζ t.val)
  h (ζ : Φ) (t : Rˣ) := (n ζ t) * (n ζ (-1))

  -- linear relation
  M_mul_add : ∀ (ζ : Φ) (t u : R), (M ζ t) * (M ζ u) = M ζ (t + u)
  -- diagonal relation
  h_mul_mul : ∀ (ζ : Φ) (t u : Rˣ), (h ζ t) * (h ζ u) = h ζ (t * u)
