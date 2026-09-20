import Mathlib.Data.Int.Basic

/-!
# Bare raw code-pair residual arithmetic

This lower module contains only the arithmetic shadow of two endpoint codes in
the even fiber `2n`.  It deliberately has no generated-shell, Boolean
atomicity, SU(7) branching, coverage, normalizer, or endpoint-observation
dependency.

The definitions retain their historical namespace, bodies, and
unfoldability.  `Proposition929` remains the first generated-shell consumer.
-/

namespace SaturationMonoid
namespace StandardModelConstraint

/-- Raw residual of two endpoint codes in the even fiber `2n`. -/
def rawCodePairResidual (n left right : ℕ) : ℤ :=
  ((left + right : ℕ) : ℤ) - ((2 * n : ℕ) : ℤ)

/-- Absolute residual energy of two endpoint codes. -/
def rawCodePairResidualEnergy (n left right : ℕ) : ℕ :=
  Int.natAbs (rawCodePairResidual n left right)

end StandardModelConstraint
end SaturationMonoid
