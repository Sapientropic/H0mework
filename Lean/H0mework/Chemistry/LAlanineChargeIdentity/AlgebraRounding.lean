import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraIntegerStability
import Mathlib.Algebra.Order.Round
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Algebra

open scoped Matrix

variable {n m : Type} [Fintype n] [Fintype m] [DecidableEq n]

def fieldCenter (L : Matrix n m ℚ) (V : m → ℚ) : n → ℚ := -(L *ᵥ V)

theorem compatible_near_center (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) (V : m → ℚ) (epsilon : ℚ) (z : n → Int)
    (bound : ∀ j, |residual B V z j| ≤ epsilon) (i : n) :
    |fieldCenter L V i - (z i : ℚ)| ≤ rowAbsSum L i * epsilon := by
  have identity : fieldCenter L V i - (z i : ℚ) = -(L *ᵥ residual B V z) i := by
    rw [residual_recovery L B leftInverse]
    simp only [fieldCenter, Pi.neg_apply, Pi.add_apply]
    ring
  rw [identity, abs_neg]
  exact mulVec_abs_le L _ epsilon bound i

theorem rounded_center_eq (L : Matrix n m ℚ) (B : Matrix m n ℚ)
    (leftInverse : L * B = 1) (V : m → ℚ) (epsilon : ℚ) (z : n → Int)
    (bound : ∀ j, |residual B V z j| ≤ epsilon)
    (margin : ∀ i, rowAbsSum L i * epsilon < 1 / 2) (i : n) :
    round (fieldCenter L V i) = z i := by
  apply round_eq_iff.mpr
  have close := abs_lt.mp ((compatible_near_center L B leftInverse V epsilon z bound i).trans_lt (margin i))
  exact ⟨by linarith [close.1], by linarith [close.2]⟩

end LAlanine40K2025.ChargeIdentity.Algebra
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
