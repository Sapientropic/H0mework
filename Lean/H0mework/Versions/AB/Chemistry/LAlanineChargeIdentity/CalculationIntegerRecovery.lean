import H0mework.Versions.AB.Chemistry.LAlanineChargeIdentity.CalculationExactRows
import H0mework.Chemistry.LAlanineChargeIdentity.AlgebraResidualScaling

set_option autoImplicit false

namespace SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
namespace LAlanine40K2025.ChargeIdentity.Recovery

open LAlanine40K2025.Force.Interface SourceData
open scoped Matrix BigOperators
noncomputable section

theorem denominator_positive : 0 < Source.inverseDenominator := by decide +kernel

theorem leftInverse_exact : Source.leftInverse * Source.selectedB = 1 :=
  Algebra.integer_leftInverse_to_rational Source.inverseNumerator Source.selectedBInteger
    Source.inverseDenominator Source.unitScale denominator_positive (by decide +kernel) ExactRows.inverseRows

theorem independentField_injective :
    Function.Injective (fun z : Atom → ℚ => Source.selectedB *ᵥ z) :=
  Algebra.fieldRead_injective Source.leftInverse Source.selectedB leftInverse_exact

theorem row_separation (i : Atom) : Algebra.rowAbsSum Source.leftInverse i * Source.epsilon < 1 / 2 := by
  rw [Source.leftInverse, Algebra.rationalMatrix_rowAbsSum]
  have margin : (2 : ℚ) * ((∑ j : Atom, |Source.inverseNumerator i j| : Int) : ℚ) <
      (Source.inverseDenominator : ℚ) * 1000000000 := by exact_mod_cast ExactRows.marginRows i
  have positive : (0 : ℚ) < Source.inverseDenominator := by exact_mod_cast denominator_positive
  change (((∑ j : Atom, |Source.inverseNumerator i j| : Int) : ℚ) / Source.inverseDenominator) *
    (1 / 1000000000) < 1 / 2
  rw [div_mul_div_comm, mul_one]
  apply (div_lt_iff₀ (mul_pos positive (by norm_num))).mpr
  linarith

theorem selectedResidual_exact (i : Atom) :
    Algebra.residual Source.selectedB Source.selectedField Source.reportedCharge i =
      (Source.reportedSelectedResidual i : ℚ) / 1000000000000000 := by
  change (parentFieldInteger (Source.selectedRows i) : ℚ) / 1000000000000 +
    (∑ j : Atom, ((Source.selectedBInteger i j : ℚ) / 1000000000000000) * (Source.reportedCharge j : ℚ)) = _
  rw [Algebra.scaled_residual_entry, ExactRows.selectedResidualRows i]

theorem selectedResidual_bound (i : Atom) :
    |Algebra.residual Source.selectedB Source.selectedField Source.reportedCharge i| ≤ Source.epsilon := by
  rw [selectedResidual_exact]
  exact Algebra.scaled_residual_bound _ (ExactRows.selectedBoundRows i)

theorem decoded_eq_reported : Source.decodedCharge = Source.reportedCharge := by
  funext i
  exact Algebra.rounded_center_eq Source.leftInverse Source.selectedB leftInverse_exact
    Source.selectedField Source.epsilon Source.reportedCharge selectedResidual_bound row_separation i

theorem decoded_positive (i : Atom) : 0 < Source.decodedCharge i := by
  rw [decoded_eq_reported]
  exact ExactRows.positiveRows i

theorem decoded_eq_original (i : Atom) : Source.decodedCharge i = parentCharge i := by
  rw [decoded_eq_reported]
  exact ExactRows.originalChargeRows i

theorem compatible_integer_unique (z : Atom → Int)
    (compatible : ∀ i, |Algebra.residual Source.selectedB Source.selectedField z i| ≤ Source.epsilon) :
    z = Source.decodedCharge := by
  rw [decoded_eq_reported]
  exact Algebra.compatible_integer_unique Source.leftInverse Source.selectedB leftInverse_exact
    Source.selectedField Source.epsilon (fun i => by linarith [row_separation i])
    z Source.reportedCharge compatible selectedResidual_bound

end
end LAlanine40K2025.ChargeIdentity.Recovery
end SaturationMonoid.NoIslandNoMagic.Consciousness.Immortality.Embodied.Molecule
