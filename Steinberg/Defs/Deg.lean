import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Use

namespace Steinberg

/-! ### Definition of Deg type -/

structure Deg (height : ℕ) where
  val : Nat
  isLe : val ≤ height

namespace Deg

instance instCoeOutNat (n : ℕ) : CoeOut (Deg n) ℕ := ⟨fun d => d.val⟩
instance instOfNat (n : outParam ℕ) : OfNat (Deg n) n := ⟨n, Nat.le_refl _⟩

protected def hAdd {n m : ℕ} (i : Deg n) (j : Deg m) : Deg (n + m) :=
  ⟨i.val + j.val, by
    have := i.isLe
    have := j.isLe
    omega
  ⟩

/--
  Decompose a number `0 ≤ i ≤ n + m` into `i₁ + i₂`, where `0 ≤ i₁ ≤ n` and `0 ≤ i₂ ≤ m`.
 -/
theorem decompose {n m : ℕ} (i : Deg (n + m)) : ∃ (i₁ : Deg n) (i₂ : Deg m), i = Deg.hAdd i₁ i₂ := by
  have ⟨vi, hi⟩ := i
  by_cases h_vi : vi ≤ n
  · use ⟨vi, h_vi⟩
    use ⟨0, Nat.zero_le _⟩
    simp [Deg.hAdd]
  · use ⟨n, Nat.le_refl _⟩
    use ⟨vi - n, by omega⟩
    simp [Deg.hAdd]
    omega

end Deg

#exit

open PositiveRootSystem

structure Deg {α : Type u} [CoeOut α ℕ] (a : α) where
  val : Nat
  isLe : val ≤ (a : Nat)

instance : CoeOut ℕ ℕ := ⟨id⟩

namespace Deg

def ofNat (n : Nat) : Deg n := ⟨n, Nat.le_refl n⟩
--instance instOfNat (n : Nat) : OfNat (Deg n) := ⟨ofNat⟩

#check HAdd

def add {a : α} {b : β} {c : γ} [CoeOut α ℕ] [CoeOut β ℕ]
    (d₁ : Deg a) (d₂ : Deg b) (h : a + b = c)

def hAdd {a : α} {b : β} [CoeOut α ℕ] [CoeOut β ℕ]
    (d₁ : Deg a) (d₂ : Deg b) : Deg ((a : Nat) + (b : Nat)) :=
      ⟨d₁.val + d₂.val, by
        have ⟨d, hd⟩ := d₁
        have ⟨e, he⟩ := d₂
        simp [*] at *
        sorry⟩

def hAdd' {a : α} {b : β} {c : outParam γ} [CoeOut α ℕ] [CoeOut β ℕ] [CoeOut γ ℕ]
    (d₁ : Deg a) (d₂ : Deg b) : Deg c :=
      ⟨d₁.val + d₂.val, by
        have ⟨d, hd⟩ := d₁
        have ⟨e, he⟩ := d₂
        simp [*] at *
        sorry⟩


bad (2 + 2)

def bad : Fin 6 → Nat := fun _ => 1

end Deg

-- structure Deg {α : Type u} [CoeOut α Nat] (a : α) where
--   val : Nat
--   isLe : val ≤ (a : Nat)

-- instance : CoeOut Nat Nat := ⟨id⟩
-- instance (n : Nat) : CoeOut (Fin n) Nat := ⟨fun v => v.val⟩

-- instance instRootCoeOut : CoeOut (Root) Nat := ⟨height⟩

-- namespace Deg

-- #check HAdd
-- -- protected
-- def hAdd {α : Type u} [CoeOut α Nat] {a b : α} (d₁ : Deg a) (d₂ : Deg b) : Deg (a + b) :=
--   ⟨d₁.val + d₂.val,

-- end Deg




-- structure Deg' (n : ℕ) where
--   mk ::
--   val : ℕ
--   h : val ≤ n

-- attribute [coe] Deg'.val

/--
  Syntax for adding two `Deg`s together, and then automatically deriving the
  proof term needed to show that the resulting value is in range.

  CC: Ideally, we would just use a `Fin` operation, but the closest I could
      find was `Fin.natAdd`, since `Fin.add` takes two `Fin`s of the same
      limit and adds their values together, modulo `n`. Since we know that
      the argument to derive the proof term for the addition probably only
      depends on height, we do that here.
-/
syntax (name := degAdd) term " +' " term : term

-- def deg_add (i₁ : Deg' n) (i₂ : Deg' m) : Deg' (n+m) :=
--   ⟨ (i₁.val+i₂.val), (by omega) ⟩

macro_rules
  -- | `($x +' $y) => `(⟨($x).val + ($y).val, by first | trivial | omega | simp [*] at *; omega⟩)
  | `($x +' $y) => `(deg_add $x $y)


end Steinberg
