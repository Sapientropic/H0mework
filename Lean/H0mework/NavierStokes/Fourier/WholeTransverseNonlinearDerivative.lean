import H0mework.NavierStokes.Restart.HalfCriticalComponentGluing

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeTransverseNonlinearDerivative

open ThreeDimensionalPeriodicCoarseFilterCore
open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientStretchingPairTable
open ThreeDimensionalVorticityCoefficientCoarseFilterProcess
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientTransverseSpaceTimeNonlinearRow
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing

noncomputable section

abbrev TransverseState := ↥wholeTransverseVorticitySubmodule

private theorem finiteBilinearPair_smul_left
    (coefficient : ℂ)
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        (coefficient • left) right pair =
      coefficient •
        finiteStateVorticityBilinearPairContribution left right pair := by
  unfold finiteStateVorticityBilinearPairContribution
    finiteStateVelocityCoefficient
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [biotSavartVelocityCoefficient_smul]
  simp [dotProduct_smul]
  module

private theorem finiteBilinearPair_smul_right
    (coefficient : ℂ)
    (left right : ComplexVorticityHilbertState)
    (pair : StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        left (coefficient • right) pair =
      coefficient •
        finiteStateVorticityBilinearPairContribution left right pair := by
  unfold finiteStateVorticityBilinearPairContribution
    finiteStateVelocityCoefficient
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [biotSavartVelocityCoefficient_smul]
  simp [smul_smul]
  module

private theorem wholeBilinear_smul_left
    (coefficient : ℂ)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        (coefficient • left) right output =
      coefficient •
        wholeStateVorticityBilinearCoefficientAt left right output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  simp_rw [finiteBilinearPair_smul_left]
  exact tsum_const_smul'' coefficient

private theorem wholeBilinear_smul_right
    (coefficient : ℂ)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        left (coefficient • right) output =
      coefficient •
        wholeStateVorticityBilinearCoefficientAt left right output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  simp_rw [finiteBilinearPair_smul_right]
  exact tsum_const_smul'' coefficient

def wholeTransverseBilinearLinear
    (output : IntegerWavevector) :
    TransverseState →ₗ[ℂ] TransverseState →ₗ[ℂ]
      ComplexCoordinateVector :=
  LinearMap.mk₂ ℂ
    (fun left right =>
      wholeStateVorticityBilinearCoefficientAt left.1 right.1 output)
    (by
      intro left₁ left₂ right
      simpa using wholeStateVorticityBilinearCoefficientAt_add_left
        left₁.1 left₂.1 right.1 left₁.2 left₂.2 output)
    (by
      intro coefficient left right
      simpa using wholeBilinear_smul_left
        coefficient left.1 right.1 output)
    (by
      intro left right₁ right₂
      simpa using wholeStateVorticityBilinearCoefficientAt_add_right
        left.1 right₁.1 right₂.1 left.2 output)
    (by
      intro coefficient left right
      simpa using wholeBilinear_smul_right
        coefficient left.1 right.1 output)

noncomputable def wholeTransverseBilinearCLM
    (output : IntegerWavevector) :
    TransverseState →L[ℂ] TransverseState →L[ℂ]
      ComplexCoordinateVector :=
  (wholeTransverseBilinearLinear output).mkContinuous₂
    (6 * Real.sqrt (integerWaveNormSq output)) (by
      intro left right
      change
        ‖wholeStateVorticityBilinearCoefficientAt
            left.1 right.1 output‖ ≤
          (6 * Real.sqrt (integerWaveNormSq output)) *
            ‖left‖ * ‖right‖
      simpa [mul_assoc] using
        wholeStateVorticityBilinearCoefficientAt_norm_le
          left.1 right.1 left.2 output)

noncomputable def wholeTransverseBilinearRealCLM
    (output : IntegerWavevector) :
    TransverseState →L[ℝ] TransverseState →L[ℝ]
      ComplexCoordinateVector :=
  (wholeTransverseBilinearCLM output).bilinearRestrictScalars ℝ

theorem wholeTransverseNonlinear_hasDerivAt
    (output : IntegerWavevector)
    (path : ℝ → TransverseState)
    (tangent : TransverseState)
    (time : ℝ)
    (pathDeriv : HasDerivAt path tangent time) :
    HasDerivAt
      (fun actual =>
        wholeStateVorticityNonlinearCoefficientAt
          (path actual).1 output)
      (wholeStateVorticityBilinearCoefficientAt
          (path time).1 tangent.1 output +
        wholeStateVorticityBilinearCoefficientAt
          tangent.1 (path time).1 output)
      time := by
  have generated :=
    (wholeTransverseBilinearRealCLM output).hasDerivAt_of_bilinear
      (fun _ => pathDeriv) (fun _ => pathDeriv)
  simpa [wholeTransverseBilinearRealCLM,
    wholeTransverseBilinearCLM,
    wholeTransverseBilinearLinear,
    wholeStateVorticityBilinearCoefficientAt_self] using generated

theorem wholeTransverseNonlinear_hasDerivWithinAt
    (output : IntegerWavevector)
    (path : ℝ → TransverseState)
    (tangent : TransverseState)
    (time : ℝ)
    (domain : Set ℝ)
    (pathDeriv : HasDerivWithinAt path tangent domain time) :
    HasDerivWithinAt
      (fun actual =>
        wholeStateVorticityNonlinearCoefficientAt
          (path actual).1 output)
      (wholeStateVorticityBilinearCoefficientAt
          (path time).1 tangent.1 output +
        wholeStateVorticityBilinearCoefficientAt
          tangent.1 (path time).1 output)
      domain time := by
  have generated :=
    (wholeTransverseBilinearRealCLM output).hasDerivWithinAt_of_bilinear
      pathDeriv pathDeriv
  simpa [wholeTransverseBilinearRealCLM,
    wholeTransverseBilinearCLM,
    wholeTransverseBilinearLinear,
    wholeStateVorticityBilinearCoefficientAt_self] using generated

end
end ThreeDimensionalVorticityCoefficientWholeTransverseNonlinearDerivative
end NavierStokes
end SaturationMonoid
