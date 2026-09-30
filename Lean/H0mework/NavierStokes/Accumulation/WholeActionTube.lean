import H0mework.NavierStokes.Restart.HalfCriticalComponentGluing

/-!
# Exact whole-row action tube

The whole Fourier generator is quadratic.  On an arbitrary transverse
physical state and transverse direction its restriction to the affine line
`state + step • direction` is therefore an exact degree-two identity.  The
quadratic row and the linearized row below are generated from the same whole
nonlinear coefficient; no trajectory, remainder, future table, or selected
contact is supplied.
-/

set_option autoImplicit false

namespace SaturationMonoid
namespace NavierStokes
namespace ThreeDimensionalVorticityCoefficientWholeActionTube

open ThreeDimensionalPeriodicIntegerCharacterCoarseFilter
open ThreeDimensionalPeriodicFilteredNavierStokesGenerator
open ThreeDimensionalVorticityCoefficientRawSourceCore
open ThreeDimensionalVorticityCoefficientFiniteSupportComplexTrajectory
open ThreeDimensionalVorticityCoefficientFixedOutputNonlinearContinuity
open ThreeDimensionalVorticityCoefficientInfiniteFixedOutputNonlinearRow
open ThreeDimensionalVorticityCoefficientCanonicalExhaustiveGalerkinTarget
open ThreeDimensionalVorticityCoefficientGeneratedWholeRestartHalfCriticalComponentGluing

noncomputable section

/-- The zero nonlinear row vanishes by pairwise transversality.  Keeping this
local algebraic mouth avoids importing a crossing-specific authority module
into the action compiler. -/
theorem wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state) :
    wholeStateVorticityNonlinearCoefficientAt state 0 = 0 := by
  unfold wholeStateVorticityNonlinearCoefficientAt
  have pairZero : ∀ first : IntegerWavevector,
      finiteStateVorticityNonlinearPairContribution
          state (first, (0 : IntegerWavevector) - first) = 0 := by
    intro first
    have secondWave :
        (0 : IntegerWavevector) - first = waveNeg first := by
      ext coordinate
      simp [waveNeg]
    have stateDot :
        complexWavevector ((0 : IntegerWavevector) - first) ⬝ᵥ
            state first = 0 := by
      rw [secondWave, complexWavevector_waveNeg]
      simpa using congrArg Neg.neg (transverse first)
    have velocityDot :
        complexWavevector ((0 : IntegerWavevector) - first) ⬝ᵥ
            finiteStateVelocityCoefficient state first = 0 := by
      rw [secondWave, complexWavevector_waveNeg, neg_dotProduct]
      simpa [finiteStateVelocityCoefficient] using
        congrArg Neg.neg
          (complexWavevector_dot_biotSavartVelocityCoefficient
            first (state first))
    unfold finiteStateVorticityNonlinearPairContribution
    rw [stateDot, velocityDot]
    simp
  simp only [pairZero]
  exact tsum_zero

theorem wholeLatticeVorticityFourierTangentAt_zero
    (viscosity : Real)
    (state : ComplexVorticityHilbertState)
    (transverse : WholeStateTransverse state)
    (zeroRow : state 0 = 0) :
    wholeLatticeVorticityFourierTangentAt viscosity state 0 = 0 := by
  unfold wholeLatticeVorticityFourierTangentAt
  rw [wholeStateVorticityNonlinearCoefficientAt_zero_of_transverse
    state transverse, zeroRow, smul_zero, sub_zero]

theorem finiteStateVorticityBilinearPairContribution_real_smul_left
    (scale : Real)
    (left right : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        (scale • left) right pair =
      (scale : Complex) •
        finiteStateVorticityBilinearPairContribution left right pair := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient_real_smul]
  module

theorem finiteStateVorticityBilinearPairContribution_real_smul_right
    (scale : Real)
    (left right : ComplexVorticityHilbertState)
    (pair :
      ThreeDimensionalVorticityCoefficientStretchingPairTable.StretchingPair) :
    finiteStateVorticityBilinearPairContribution
        left (scale • right) pair =
      (scale : Complex) •
        finiteStateVorticityBilinearPairContribution left right pair := by
  simp [finiteStateVorticityBilinearPairContribution,
    finiteStateVelocityCoefficient_real_smul]
  module

theorem wholeStateVorticityBilinearCoefficientAt_real_smul_left
    (scale : Real)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        (scale • left) right output =
      (scale : Complex) •
        wholeStateVorticityBilinearCoefficientAt left right output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  simp_rw [finiteStateVorticityBilinearPairContribution_real_smul_left]
  rw [tsum_const_smul'']

theorem wholeStateVorticityBilinearCoefficientAt_real_smul_right
    (scale : Real)
    (left right : ComplexVorticityHilbertState)
    (output : IntegerWavevector) :
    wholeStateVorticityBilinearCoefficientAt
        left (scale • right) output =
      (scale : Complex) •
        wholeStateVorticityBilinearCoefficientAt left right output := by
  unfold wholeStateVorticityBilinearCoefficientAt
  simp_rw [finiteStateVorticityBilinearPairContribution_real_smul_right]
  rw [tsum_const_smul'']

/-- Exact first action coordinate of the whole Fourier generator. -/
def wholeGeneratorLinearizationRow
    (viscosity : Real)
    (state direction : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeStateVorticityBilinearCoefficientAt direction state output +
      wholeStateVorticityBilinearCoefficientAt state direction output -
    (viscosity * integerWaveViscousMultiplier output) • direction output

/-- Exact second action coordinate of the whole Fourier generator. -/
def wholeGeneratorQuadraticRow
    (direction : ComplexVorticityHilbertState)
    (output : IntegerWavevector) : ComplexCoordinateVector :=
  wholeStateVorticityNonlinearCoefficientAt direction output

/-- The whole NS Fourier generator restricted to an arbitrary transverse
affine action line.  This is an equality, not a Taylor estimate. -/
theorem wholeLatticeVorticityFourierTangentAt_affine_eq_actionTube
    (viscosity step : Real)
    (state direction : ComplexVorticityHilbertState)
    (stateTransverse : WholeStateTransverse state)
    (directionTransverse : WholeStateTransverse direction)
    (output : IntegerWavevector) :
    wholeLatticeVorticityFourierTangentAt viscosity
        (state + step • direction) output =
      wholeLatticeVorticityFourierTangentAt viscosity state output +
        step • wholeGeneratorLinearizationRow viscosity state direction output +
        step ^ 2 • wholeGeneratorQuadraticRow direction output := by
  rw [wholeLatticeVorticityFourierTangentAt,
    wholeLatticeVorticityFourierTangentAt]
  rw [wholeStateVorticityNonlinearCoefficientAt_add
    state (step • direction) stateTransverse
    (wholeStateTransverse_real_smul step direction directionTransverse) output]
  rw [wholeStateVorticityNonlinearCoefficientAt_real_smul,
    wholeStateVorticityBilinearCoefficientAt_real_smul_right,
    wholeStateVorticityBilinearCoefficientAt_real_smul_left]
  simp only [lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply]
  unfold wholeGeneratorLinearizationRow wholeGeneratorQuadraticRow
  module

end
end ThreeDimensionalVorticityCoefficientWholeActionTube
end NavierStokes
end SaturationMonoid
